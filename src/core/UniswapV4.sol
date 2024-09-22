// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {SettlerAbstract} from "../SettlerAbstract.sol";

import {Panic} from "../utils/Panic.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";

import {
    TooMuchSlippage,
    DeltaNotPositive,
    DeltaNotNegative,
    ZeroBuyAmount,
    BoughtSellToken,
    TokenHashCollision,
    ZeroToken
} from "./SettlerErrors.sol";

import {
    BalanceDelta, IHooks, IPoolManager, UnsafePoolManager, POOL_MANAGER, IUnlockCallback
} from "./UniswapV4Types.sol";

library CreditDebt {
    using UnsafeMath for int256;

    function asCredit(int256 delta, IERC20 token) internal pure returns (uint256) {
        if (delta < 0) {
            revert DeltaNotPositive(token);
        }
        return uint256(delta);
    }

    function asDebt(int256 delta, IERC20 token) internal pure returns (uint256) {
        if (delta > 0) {
            revert DeltaNotNegative(token);
        }
        return uint256(delta.unsafeNeg());
    }
}

library MemptrAndTokenLib {
    type MemPtr is uint24;
    type MemptrAndToken is uint256;

    uint256 private constant _ADDRESS_MASK = 0x00ffffffffffffffffffffffffffffffffffffffff;
    uint256 private constant _U24_MASK = 0xffffff;

    function construct(uint24 memptr, IERC20 tokenAddr) internal pure returns (MemptrAndToken r) {
        assembly ("memory-safe") {
            r := or(shl(0xe8, memptr), and(_ADDRESS_MASK, tokenAddr))
        }
    }

    function ptr(MemptrAndToken x) internal pure returns (MemPtr r) {
        assembly ("memory-safe") {
            r := shr(0xe8, x)
        }
    }

    function token(MemptrAndToken x) internal pure returns (IERC20 r) {
        assembly ("memory-safe") {
            r := x
        }
    }

    function isNull(MemPtr x) internal pure returns (bool r) {
        assembly ("memory-safe") {
            r := iszero(and(_U24_MASK, x))
        }
    }
}

/// This library is a highly-optimized, in-memory, enumerable mapping from tokens to amounts. It
/// consists of 2 components that must be kept synchronized. There is a `memory` array of `Note`
/// (aka `Note[] memory`) that has up to `_MAX_TOKENS` pre-allocated. And there is an implicit heap
/// packed at the end of the array that stores the `Note`s. Each `Note` has a backpointer that knows
/// its location in the `Notes[] memory`. While the length of the `Notes[]` array grows and shrinks
/// as tokens are added and retired, heap objects are only cleared/deallocated when the context of
/// `unlockCallback` returns. Looking up the `Note` object corresponding to a token uses the perfect
/// hash formed by `hashMul` and `hashMod`. Pay special attention to these parameters. See further
/// below in `contract UniswapV4` for recommendations on how to select values for them. A hash
/// collision will result in a revert with signature `TokenHashCollision(address,address)`.
library NotesLib {
    using MemptrAndTokenLib for MemptrAndTokenLib.MemPtr;
    using MemptrAndTokenLib for MemptrAndTokenLib.MemptrAndToken;

    uint256 private constant _ADDRESS_MASK = 0x00ffffffffffffffffffffffffffffffffffffffff;

    /// This is the maximum number of tokens that may be involved in a UniV4 action. Increasing or
    /// decreasing this value requires no other changes elsewhere in this file.
    uint256 private constant _MAX_TOKENS = 8;

    struct Note {
        uint256 amount;
        MemptrAndTokenLib.MemptrAndToken tokenAndBackptr;
    }

    type NotePtr is uint256;

    function construct() internal pure returns (Note[] memory r) {
        assembly ("memory-safe") {
            r := mload(0x40)
            // set the length of `r` to zero
            mstore(r, 0x00)
            // zeroize the heap
            codecopy(add(add(0x20, shl(0x05, _MAX_TOKENS)), r), codesize(), shl(0x06, _MAX_TOKENS))
            // allocate memory
            mstore(0x40, add(add(0x20, mul(0x60, _MAX_TOKENS)), r))
        }
    }

    function eq(Note memory x, Note memory y) internal pure returns (bool r) {
        assembly ("memory-safe") {
            r := eq(x, y)
        }
    }

    function get(Note memory x) internal pure returns (IERC20, uint256) {
        return (x.tokenAndBackptr.token(), x.amount);
    }

    function token(Note memory x) internal pure returns (IERC20) {
        return x.tokenAndBackptr.token();
    }

    function get(Note[] memory a, uint256 i) internal pure returns (IERC20 retToken, uint256 retAmount) {
        assembly ("memory-safe") {
            let x := mload(add(add(0x20, shl(0x05, i)), a))
            retToken := mload(add(0x20, x))
            retAmount := mload(x)
        }
    }

    function get(Note[] memory a, IERC20 newToken, uint256 hashMul, uint256 hashMod)
        internal
        pure
        returns (NotePtr x)
    {
        assembly ("memory-safe") {
            newToken := and(_ADDRESS_MASK, newToken)
            x := add(add(0x20, shl(0x05, _MAX_TOKENS)), a) // `x` now points at the first `Note` on the heap
            x := add(mod(mulmod(newToken, hashMul, hashMod), shl(0x06, _MAX_TOKENS)), x) // combine with token hash
            // `x` now points at the exact `Note` object we want; let's check it to be sure, though

            // load the old value of the metadata slot so that we can check it
            let x_tokenbackptr_ptr := add(0x20, x)
            let old_tokenbackptr := mload(x_tokenbackptr_ptr)

            // check that we haven't encountered a hash collision
            let old_backptr := shr(0xe8, old_tokenbackptr)
            {
                let old_token := and(_ADDRESS_MASK, old_tokenbackptr)
                if mul(or(old_backptr, old_token), xor(old_token, newToken)) { // TODO(dekz): check me on this?
                    mstore(0x00, 0x9a62e8b4) // selector for `TokenHashCollision(address,address)`
                    mstore(0x20, old_token)
                    mstore(0x40, newToken)
                    revert(0x1c, 0x44)
                }
            }

            // zero `newToken` is a footgun; check for it
            if iszero(newToken) {
                mstore(0x00, 0xad1991f5) // selector for `ZeroToken()`
                revert(0x1c, 0x04)
            }

            // initialize the metadata slot
            mstore(x_tokenbackptr_ptr, or(shl(0xe8, old_backptr), newToken))
        }
    }

    function initialize(Note[] memory a, NotePtr x, IERC20 initToken) internal pure {
        assembly ("memory-safe") {
            initToken := and(_ADDRESS_MASK, initToken)
            if iszero(initToken) {
                mstore(0x00, 0xad1991f5) // selector for `ZeroToken()`
                revert(0x1c, 0x04)
            }
            mstore(a, 0x01)
            let x_ptr := add(0x20, a)
            mstore(x_ptr, x)
            mstore(add(0x20, x), or(shl(0xe8, x_ptr), initToken))
        }
    }

    function add(Note[] memory a, Note memory x) internal pure {
        assembly ("memory-safe") {
            let tokenbackptr_ptr := add(0x20, x)
            let tokenbackptr := mload(tokenbackptr_ptr)
            if iszero(shr(0xe8, tokenbackptr)) {
                let len := add(0x01, mload(a))
                // We don't need to check for overflow or out-of-bounds access here; the checks in
                // `get` above for token collision handle that for us. It's not possible to `get`
                // more than `_MAX_TOKENS` tokens
                mstore(a, len)
                let x_ptr := add(shl(0x05, len), a)
                mstore(x_ptr, x)

                // The 3 high bytes of `tokenbackptr` are clear.
                tokenbackptr := or(shl(0xe8, x_ptr), tokenbackptr)
                mstore(tokenbackptr_ptr, tokenbackptr)
            }
        }
    }

    function del(Note[] memory a, Note memory x) internal pure {
        assembly ("memory-safe") {
            let x_tokenbackptr_ptr := add(0x20, x)
            let x_tokenbackptr := mload(x_tokenbackptr_ptr)
            let x_ptr := shr(0xe8, x_tokenbackptr)
            if x_ptr {
                // Clear the backpointer in the referred-to `Note`
                mstore(x_tokenbackptr_ptr, and(_ADDRESS_MASK, x_tokenbackptr))
                // We do not deallocate `x`

                // Check if this is a "swap and pop" or just a "pop"
                let len := mload(a)
                let end_ptr := add(shl(0x05, len), a)
                if iszero(eq(end_ptr, x_ptr)) {
                    // Overwrite the vacated indirection pointer `x_ptr` with the one at the end.
                    let end := mload(end_ptr)
                    mstore(x_ptr, end)

                    // Fix up the backpointer in `end` to point to the new location of the indirection
                    // pointer.
                    let end_tokenbackptr_ptr := add(0x20, end)
                    let end_tokenbackptr := mload(end_tokenbackptr_ptr)
                    end_tokenbackptr := or(shl(0xe8, x_ptr), and(_ADDRESS_MASK, end_tokenbackptr))
                    mstore(end_tokenbackptr_ptr, end_tokenbackptr)
                }

                // Decrement the length of `a`
                mstore(a, sub(len, 0x01))
            }
        }
    }
}

library StateLib {
    using NotesLib for NotesLib.Note;
    using NotesLib for NotesLib.Note[];

    struct State {
        NotesLib.Note buy;
        NotesLib.Note sell;
        NotesLib.Note globalSell;
        uint256 globalSellAmount;
        uint256 _hashMul;
        uint256 _hashMod;
    }

    function construct(State memory state, IERC20 token, uint256 hashMul, uint256 hashMod)
        internal
        pure
        returns (NotesLib.Note[] memory notes)
    {
        assembly ("memory-safe") {
            // Solc is real dumb and has allocated a bunch of extra memory for us. Thanks solc.
            if iszero(eq(mload(0x40), add(0x180, state))) { revert(0x00, 0x00) }
            mstore(0x40, add(0xc0, state))
        }
        // All the pointers in `state` are now pointing into unallocated memory
        notes = NotesLib.construct();
        // The pointers in `state` are now illegally aliasing elements in `notes`
        NotesLib.NotePtr notePtr = notes.get(token, hashMul, hashMod);
        notes.initialize(notePtr, token);

        // Here we actually set the pointers into a legal area of memory
        setBuy(state, notePtr);
        setSell(state, notePtr);
        assembly ("memory-safe") {
            // Set `state.globalSell`
            mstore(add(0x40, state), notePtr)
        }
        state._hashMul = hashMul;
        state._hashMod = hashMod;
    }

    function setSell(State memory state, NotesLib.NotePtr notePtr) private pure {
        assembly ("memory-safe") {
            mstore(add(0x20, state), notePtr)
        }
    }

    function setSell(State memory state, NotesLib.Note[] memory notes, IERC20 token) internal pure {
        setSell(state, notes.get(token, state._hashMul, state._hashMod));
    }

    function setBuy(State memory state, NotesLib.NotePtr notePtr) private pure {
        assembly ("memory-safe") {
            mstore(state, notePtr)
        }
    }

    function setBuy(State memory state, NotesLib.Note[] memory notes, IERC20 token) internal pure {
        setBuy(state, notes.get(token, state._hashMul, state._hashMod));
    }
}

abstract contract UniswapV4 is SettlerAbstract {
    using SafeTransferLib for IERC20;
    using UnsafeMath for uint256;
    using UnsafeMath for int256;
    using CreditDebt for int256;
    using MemptrAndTokenLib for MemptrAndTokenLib.MemPtr;
    using MemptrAndTokenLib for MemptrAndTokenLib.MemptrAndToken;
    using UnsafePoolManager for IPoolManager;
    using NotesLib for NotesLib.Note;
    using NotesLib for NotesLib.Note[];
    using StateLib for StateLib.State;

    //// These two functions are the entrypoints to this set of actions. Because UniV4 has a
    //// mandatory callback, and the vast majority of the business logic has to be executed inside
    //// the callback, they're pretty minimal. Both end up inside the last function in this file
    //// `unlockCallback`, which is where most of the business logic lives. Primarily, these
    //// functions are concerned with correctly encoding the argument to
    //// `POOL_MANAGER.unlock(...)`. Pay special attention to the `payer` field, which is what
    //// signals to the callback whether we should be spending a coupon.

    //// How to generate `fills` for UniV4:
    ////
    //// Linearize your DAG of fills by doing a topological sort on the tokens involved. In the
    //// topological sort of tokens, when there is a choice of the next token, break ties by
    //// preferring a token if it is the lexicographically largest token that is bought among fills
    //// with sell token equal to the previous token in the topological sort. Then sort the fills
    //// belonging to each sell token by their buy token. This technique isn't *quite* optimal, but
    //// it's pretty close. The buy token of the final fill is special-cased. It is the token that
    //// will be transferred to `recipient` and have its slippage checked against `amountOutMin`. In
    //// the event that you are encoding a series of fills with more than one output token, ensure
    //// that at least one of the global buy token's fills is positioned appropriately.
    ////
    //// Now that you have a list of fills, encode each fill as follows.
    //// First encode the `bps` for the fill as 2 bytes. Remember that this `bps` is relative to the
    //// running balance at the moment that the fill is settled.
    //// Second, encode the packing key for that fill as 1 byte. The packing key byte depends on the
    //// tokens involved in the previous fill. The packing key for the first fill must be 1;
    //// i.e. encode only the buy token for the first fill.
    ////   0 -> sell and buy tokens remain unchanged from the previous fill (pure multiplex)
    ////   1 -> sell token remains unchanged from the previous fill, buy token is encoded (diamond multiplex)
    ////   2 -> sell token becomes the buy token from the previous fill, new buy token is encoded (multihop)
    ////   3 -> both sell and buy token are encoded
    //// Obviously, after encoding the packing key, you encode 0, 1, or 2 tokens (each as 20 bytes),
    //// as appropriate.
    //// The remaining fields of the fill are mandatory.
    //// Third, encode the pool fee as 3 bytes, and the pool tick spacing as 3 bytes.
    //// Fourth, encode the hook address as 20 bytes.
    //// Fifth, encode the hook data for the fill. Encode the length of the hook data as 3 bytes,
    //// then append the hook data itself.
    ////
    //// Repeat the process for each fill and concatenate the results without padding.

    //// How to generate a perfect hash for UniV4:
    ////
    //// The arguments `hashMul` and `hashMod` are required to form a perfect hash for a table with
    //// size `_MAX_TOKENS` when applied to all the tokens involved in fills. The hash function is
    //// constructed as `uint256 hash = mulmod(uint256(uint160(address(token))), hashMul, hashMod) %
    //// _MAX_TOKENS`.
    ////
    //// The "simple" or "obvious" way to do this is to simply try random 128-bit numbers for both
    //// `hashMul` and `hashMod` until you obtain a function that has no collisions when applied to
    //// the tokens involved in fills. A substantially more optimized algorithm can be obtained by
    //// selecting several (at least 10) prime values for `hashMod`, precomputing the limb moduluses
    //// for each value, and then selecting randomly from among them. The author recommends using
    //// the 10 largest 64-bit prime numbers: 2^64 - {59, 83, 95, 179, 189, 257, 279, 323, 353,
    //// 363}. `hashMul` can then be selected randomly or via some other optimized method.
    ////
    //// Note that in spite of the fact that the pool manager represents Ether (or the native asset
    //// of the chain) as `address(0)`, we represent Ether as `SettlerAbstract.ETH_ADDRESS` (the
    //// address of all `e`s) for homogeneity with other parts of the codebase, and because the
    //// decision to represent Ether as `address(0)` was stupid in the first place. `address(0)`
    //// represents the absence of a thing, not a special case of the thing. It creates confusion
    //// with uninitialized memory, storage, and variables.

    function sellToUniswapV4(
        address recipient,
        IERC20 sellToken,
        uint256 bps,
        bool feeOnTransfer,
        uint256 hashMul,
        uint256 hashMod,
        bytes memory fills,
        uint256 amountOutMin
    ) internal returns (uint256) {
        if (amountOutMin > uint128(type(int128).max)) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }
        if (bps > BASIS) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }
        hashMul *= 64;
        hashMod *= 64;
        if (hashMul > type(uint128).max) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }
        if (hashMod > type(uint128).max) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }
        bytes memory data;
        assembly ("memory-safe") {
            data := mload(0x40)

            let pathLen := mload(fills)
            mcopy(add(0xd3, data), add(0x20, fills), pathLen)

            mstore(add(0xb3, data), bps)
            mstore(add(0xb1, data), sellToken)
            mstore(add(0x9d, data), address()) // payer
            // feeOnTransfer (1 byte)

            mstore(add(0x88, data), hashMod)
            mstore(add(0x78, data), hashMul)
            mstore(add(0x68, data), amountOutMin)
            mstore(add(0x58, data), recipient)
            mstore(add(0x44, data), add(0x6f, pathLen))
            mstore(add(0x24, data), 0x20)
            mstore(add(0x04, data), 0x48c89491) // selector for `unlock(bytes)`
            mstore(data, add(0xb3, pathLen))
            mstore8(add(0xa8, data), feeOnTransfer)

            mstore(0x40, add(data, add(0xd3, pathLen)))
        }
        return abi.decode(
            abi.decode(
                _setOperatorAndCall(
                    address(POOL_MANAGER), data, uint32(IUnlockCallback.unlockCallback.selector), _uniV4Callback
                ),
                (bytes)
            ),
            (uint256)
        );
    }

    function sellToUniswapV4VIP(
        address recipient,
        bool feeOnTransfer,
        uint256 hashMul,
        uint256 hashMod,
        bytes memory fills,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes memory sig,
        uint256 amountOutMin
    ) internal returns (uint256) {
        if (amountOutMin > uint128(type(int128).max)) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }
        hashMul *= 64;
        hashMod *= 64;
        if (hashMul > type(uint128).max) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }
        if (hashMod > type(uint128).max) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }
        bool isForwarded = _isForwarded();
        bytes memory data;
        assembly ("memory-safe") {
            data := mload(0x40)

            let pathLen := mload(fills)
            let sigLen := mload(sig)

            {
                let ptr := add(0x132, data)

                // sig length as 3 bytes goes at the end of the callback
                mstore(sub(add(sigLen, add(pathLen, ptr)), 0x1d), sigLen)

                // fills go at the end of the header
                mcopy(ptr, add(0x20, fills), pathLen)
                ptr := add(pathLen, ptr)

                // signature comes after the fills
                mcopy(ptr, add(0x20, sig), sigLen)
                ptr := add(sigLen, ptr)

                mstore(0x40, add(0x03, ptr))
            }

            mstore8(add(0x131, data), isForwarded)
            mcopy(add(0xf1, data), add(0x20, permit), 0x40)
            mcopy(add(0xb1, data), mload(permit), 0x40) // aliases `payer` on purpose
            mstore(add(0x9d, data), 0x00) // payer
            // feeOnTransfer (1 byte)

            mstore(add(0x88, data), hashMod)
            mstore(add(0x78, data), hashMul)
            mstore(add(0x68, data), amountOutMin)
            mstore(add(0x58, data), recipient)
            mstore(add(0x44, data), add(0xd1, add(pathLen, sigLen)))
            mstore(add(0x24, data), 0x20)
            mstore(add(0x04, data), 0x48c89491) // selector for `unlock(bytes)`
            mstore(data, add(0x115, add(pathLen, sigLen)))

            mstore8(add(0xa8, data), feeOnTransfer)

            // TODO: remove
            if iszero(eq(add(mload(data), add(0x20, data)), mload(0x40))) { revert(0x00, 0x00) }
        }
        return abi.decode(
            abi.decode(
                _setOperatorAndCall(
                    address(POOL_MANAGER), data, uint32(IUnlockCallback.unlockCallback.selector), _uniV4Callback
                ),
                (bytes)
            ),
            (uint256)
        );
    }

    function _uniV4Callback(bytes calldata data) private returns (bytes memory) {
        // We know that our calldata is well-formed. Therefore, the first slot is 0x20 and the
        // second slot is the length of the strict ABIEncoded payload
        assembly ("memory-safe") {
            data.length := calldataload(add(0x20, data.offset))
            data.offset := add(0x40, data.offset)
        }
        return unlockCallback(data);
    }

    //// The following functions are the helper functions for `unlockCallback`. They abstract much
    //// of the complexity of tracking which tokens need to be zeroed out at the end of the
    //// callback.
    ////
    //// The two major pieces of state that are maintained through the callback are `Note[] memory
    //// notes` and `State memory state`
    ////
    //// `notes` keeps track of the list of the tokens that have been touched throughout the
    //// callback that have nonzero credit. At the end of the fills, all tokens with credit will be
    //// swept back to Settler. These are the global buy token (against which slippage is checked)
    //// and any other multiplex-out tokens. Only the global sell token is allowed to have debt, but
    //// it is accounted slightly differently from the other tokens. The function `_take` is
    //// responsible for iterating over the list of tokens and withdrawing any credit to the
    //// appropriate recipient.
    ////
    //// `state` exists to reduce stack pressure and to simplify/gas-optimize the process of
    //// swapping. By keeping track of the sell and buy token on each hop, we're able to compress
    //// the representation of the fills required to satisfy the swap. Most often in a swap, the
    //// tokens in adjacent fills are somewhat in common. By caching, we avoid having them appear
    //// multiple times in the calldata.

    // the mandatory fields are
    // 2 - sell bps
    // 1 - pool key tokens case
    // 3 - pool fee
    // 3 - pool tick spacing
    // 20 - pool hooks
    // 3 - hook data length
    uint256 private constant _HOP_DATA_LENGTH = 32;

    /// Update `state` for the next fill packed in `data`. This also may allocate/append `Note`s
    /// into `notes`. Returns the suffix of the bytes that are not consumed in the decoding
    /// process. The first byte of `data` describes which of the compact representations for the hop
    /// is used.
    ///
    ///   0 -> sell and buy tokens remain unchanged from the previous fill (pure multiplex)
    ///   1 -> sell token remains unchanged from the previous fill, buy token is read from `data` (diamond multiplex)
    ///   2 -> sell token becomes the buy token from the previous fill, new buy token is read from `data` (multihop)
    ///   3 -> both sell and buy token are read from `data`
    ///
    /// This function is responsible for calling `NotesLib.get(Note[] memory, IERC20, uint256,
    /// uint256)` (via `StateLib.setSell` and `StateLib.setBuy`), which maintains the `notes` array
    /// and heap.
    function _updateState(StateLib.State memory state, NotesLib.Note[] memory notes, bytes calldata data)
        private
        pure
        returns (bytes calldata)
    {
        uint256 caseKey = uint8(bytes1(data));
        data = data[1:];
        if (caseKey != 0) {
            if (caseKey > 1) {
                if (state.sell.amount == 0) {
                    notes.del(state.sell);
                }
                if (caseKey == 2) {
                    state.sell = state.buy;
                } else {
                    assert(caseKey == 3);

                    IERC20 sellToken = IERC20(address(uint160(bytes20(data))));
                    data = data[20:];

                    state.setSell(notes, sellToken);
                }
            }

            if (state.buy.amount != 0) {
                notes.add(state.buy);
            }

            IERC20 buyToken = IERC20(address(uint160(bytes20(data))));
            data = data[20:];

            state.setBuy(notes, buyToken);
            if (state.buy.eq(state.globalSell)) {
                revert BoughtSellToken(state.globalSell.token());
            }
        }
        return data;
    }

    uint256 private constant _ADDRESS_MASK = 0x00ffffffffffffffffffffffffffffffffffffffff;

    /// Decode a `PoolKey` from its packed representation in `bytes` and the token information in
    /// `state`. Returns the `zeroForOne` flag and the suffix of the bytes that are not consumed in
    /// the decoding process.
    function _setPoolKey(IPoolManager.PoolKey memory key, StateLib.State memory state, bytes calldata data)
        private
        pure
        returns (bool, bytes calldata)
    {
        (IERC20 sellToken, IERC20 buyToken) = (state.sell.token(), state.buy.token());
        bool zeroForOne;
        assembly ("memory-safe") {
            sellToken := and(_ADDRESS_MASK, sellToken)
            buyToken := and(_ADDRESS_MASK, buyToken)
            zeroForOne :=
                or(
                    eq(sellToken, 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee),
                    and(iszero(eq(buyToken, 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee)), lt(sellToken, buyToken))
                )
        }
        (key.token0, key.token1) = zeroForOne ? (sellToken, buyToken) : (buyToken, sellToken);
        uint256 packed = uint208(bytes26(data));
        data = data[26:];
        key.fee = uint24(packed >> 184);
        key.tickSpacing = int24(uint24(packed >> 160));
        key.hooks = IHooks.wrap(address(uint160(packed)));
        return (zeroForOne, data);
    }

    /// Decode an ABI-ish encoded `bytes` from `data`. It is "-ish" in the sense that the encoding
    /// of the length doesn't take up an entire word. The length is encoded as only 3 bytes (2^24
    /// bytes of calldata consumes ~67M gas, much more than the block limit). The payload is also
    /// unpadded. The next fill's `bps` is encoded immediately after the `hookData` payload.
    function _getHookData(bytes calldata data) private pure returns (bytes calldata hookData, bytes calldata retData) {
        assembly ("memory-safe") {
            hookData.length := shr(0xe8, calldataload(data.offset))
            hookData.offset := add(0x03, data.offset)
            let hop := add(0x03, hookData.length)
            retData.offset := add(data.offset, hop)
            retData.length := sub(data.length, hop)
            if gt(retData.length, 0xffffff) { // length underflow
                mstore(0x00, 0x4e487b71) // selector for `Panic(uint256)`
                mstore(0x20, 0x32) // array out-of-bounds
                revert(0x1c, 0x24)
            }
        }
    }

    /// `_take` is responsible for removing the accumulated credit in each token from the pool
    /// manager. The current `state.buy` is the global buy token. We return the settled amount of
    /// that token (`buyAmount`), after checking it against the slippage limit
    /// (`minBuyAmount`). Each token with credit causes a corresponding call to `POOL_MANAGER.take`.
    function _take(StateLib.State memory state, NotesLib.Note[] memory notes, address recipient, uint256 minBuyAmount)
        private
        returns (uint256 buyAmount)
    {
        if (state.buy.amount == 0) {
            revert ZeroBuyAmount(state.buy.token());
        }
        notes.del(state.buy);
        if (state.sell.amount == 0) {
            notes.del(state.sell);
        }

        uint256 length = notes.length;
        // `length` of zero implies that we fully liquidated the global sell token (there is no
        // `amount` remaining) and that the only token in which we have credit is the global buy
        // token. We're about to `take` that token below.
        if (length != 0) {
            {
                NotesLib.Note memory firstNote = notes[0]; // out-of-bounds is impossible
                if (!firstNote.eq(state.globalSell)) {
                    // The global sell token being in a position other than the 1st would imply that
                    // at some point we _bought_ that token. This is illegal and results in a revert
                    // with reason `BoughtSellToken(address)`.
                    IPoolManager(_operator()).unsafeTake(firstNote.token(), address(this), firstNote.amount);
                }
            }
            for (uint256 i = 1; i < length; i = i.unsafeInc()) {
                (IERC20 token, uint256 amount) = notes.get(i);
                IPoolManager(_operator()).unsafeTake(token, address(this), amount);
            }
        }

        // The final token to be bought is considered the global buy token. We bypass `notes` and
        // read it directly from `state`. Check the slippage limit. Transfer to the recipient.
        {
            IERC20 buyToken;
            (buyToken, buyAmount) = state.buy.get();
            if (buyAmount < minBuyAmount) {
                revert TooMuchSlippage(buyToken, minBuyAmount, buyAmount);
            }
            IPoolManager(_operator()).unsafeTake(buyToken, recipient, buyAmount);
        }
    }

    function _pay(
        IERC20 sellToken,
        address payer,
        uint256 sellAmount,
        ISignatureTransfer.PermitTransferFrom calldata permit,
        bool isForwarded,
        bytes calldata sig
    ) private returns (uint256) {
        IPoolManager(_operator()).unsafeSync(sellToken);
        if (payer == address(this)) {
            sellToken.safeTransfer(_operator(), sellAmount);
        } else {
            // assert(payer == address(0));
            ISignatureTransfer.SignatureTransferDetails memory transferDetails =
                ISignatureTransfer.SignatureTransferDetails({to: _operator(), requestedAmount: sellAmount});
            _transferFrom(permit, transferDetails, sig, isForwarded);
        }
        return IPoolManager(_operator()).settle();
    }

    function _initialize(bytes calldata data, bool feeOnTransfer, uint256 hashMul, uint256 hashMod, address payer)
        private
        returns (
            bytes calldata newData,
            StateLib.State memory state,
            NotesLib.Note[] memory notes,
            ISignatureTransfer.PermitTransferFrom calldata permit,
            bool isForwarded,
            bytes calldata sig
        )
    {
        {
            IERC20 sellToken = IERC20(address(uint160(bytes20(data))));
            // We don't advance `data` here because there's a special interaction between `payer`,
            // `sellToken`, and `permit` that's handled below.
            notes = state.construct(sellToken, hashMul, hashMod);
        }

        // This assembly block is just here to appease the compiler. We only use `permit` and `sig`
        // in the codepaths where they are set away from the values initialized here.
        assembly ("memory-safe") {
            permit := calldatasize()
            sig.offset := calldatasize()
            sig.length := 0x00
        }

        if (state.globalSell.token() == ETH_ADDRESS) {
            assert(payer == address(this));
            data = data[20:]; // advance `data` from decoding `sellToken` above

            uint16 bps = uint16(bytes2(data));
            data = data[2:];
            unchecked {
                state.globalSell.amount = (address(this).balance * bps).unsafeDiv(BASIS);
            }
        } else {
            if (payer == address(this)) {
                data = data[20:]; // advance `data` from decoding `sellToken` above

                uint16 bps = uint16(bytes2(data));
                data = data[2:];
                unchecked {
                    state.globalSell.amount = (state.globalSell.token().balanceOf(address(this)) * bps).unsafeDiv(BASIS);
                }
            } else {
                assert(payer == address(0));

                assembly ("memory-safe") {
                    // this is super dirty, but it works because although `permit` is aliasing in
                    // the middle of `payer`, because `payer` is all zeroes, it's treated as padding
                    // for the first word of `permit`, which is the sell token
                    permit := sub(data.offset, 0x0c)
                    isForwarded := and(0x01, calldataload(add(0x55, data.offset)))

                    // `sig` is packed at the end of `data`, in "reverse ABI-ish encoded" fashion
                    sig.offset := sub(add(data.offset, data.length), 0x03)
                    sig.length := shr(0xe8, calldataload(sig.offset))
                    sig.offset := sub(sig.offset, sig.length)

                    // Remove `permit` and `isForwarded` from the front of `data`
                    data.offset := add(0x75, data.offset)
                    if gt(data.offset, sig.offset) { revert(0x00, 0x00) }

                    // Remove `sig` from the back of `data`
                    data.length := sub(sub(data.length, 0x78), sig.length)
                    if gt(data.length, 0xffffff) { // length underflow
                        mstore(0x00, 0x4e487b71) // selector for `Panic(uint256)`
                        mstore(0x20, 0x32) // array out-of-bounds
                        revert(0x1c, 0x24)
                    }
                }

                state.globalSell.amount = _permitToSellAmountCalldata(permit);
            }

            if (feeOnTransfer) {
                state.globalSell.amount =
                    _pay(state.globalSell.token(), payer, state.globalSell.amount, permit, isForwarded, sig);
            }
        }

        state.globalSellAmount = state.globalSell.amount;
        newData = data;
    }

    function unlockCallback(bytes calldata data) private returns (bytes memory) {
        // These values are user-supplied
        address recipient = address(uint160(bytes20(data)));
        data = data[20:];
        uint256 minBuyAmount = uint128(bytes16(data));
        data = data[16:];
        uint256 hashMul = uint128(bytes16(data));
        data = data[16:];
        uint256 hashMod = uint128(bytes16(data));
        data = data[16:];
        bool feeOnTransfer = uint8(bytes1(data)) != 0;
        data = data[1:];

        // `payer` is special and is authenticated
        address payer = address(uint160(bytes20(data)));
        data = data[20:];

        // Set up `state` and `notes`. The other values are ancillary and might be used when we need
        // to settle global sell token debt at the end of swapping.
        (
            bytes calldata newData,
            StateLib.State memory state,
            NotesLib.Note[] memory notes,
            ISignatureTransfer.PermitTransferFrom calldata permit,
            bool isForwarded,
            bytes calldata sig
        ) = _initialize(data, feeOnTransfer, hashMul, hashMod, payer);
        data = newData;

        // Now that we've unpacked and decoded the header, we can begin decoding the array of swaps
        // and executing them.
        IPoolManager.PoolKey memory key;
        IPoolManager.SwapParams memory params;
        while (data.length >= _HOP_DATA_LENGTH) {
            uint16 bps = uint16(bytes2(data));
            data = data[2:];

            data = _updateState(state, notes, data);
            bool zeroForOne;
            (zeroForOne, data) = _setPoolKey(key, state, data);
            bytes calldata hookData;
            (hookData, data) = _getHookData(data);

            params.zeroForOne = zeroForOne;
            unchecked {
                params.amountSpecified = int256((state.sell.amount * bps).unsafeDiv(BASIS)).unsafeNeg();
            }
            // TODO: price limits
            params.sqrtPriceLimitX96 = zeroForOne ? 4295128740 : 1461446703485210103287273052203988822378723970341;

            BalanceDelta delta = IPoolManager(_operator()).unsafeSwap(key, params, hookData);
            {
                (int256 settledSellAmount, int256 settledBuyAmount) =
                    zeroForOne ? (delta.amount0(), delta.amount1()) : (delta.amount1(), delta.amount0());
                // Some insane hooks may increase the sell amount; obviously this may result in
                // unavoidable reverts in some cases. But we still need to make sure that we don't
                // underflow to avoid wildly unexpected behavior. The pool manager enforces that the
                // settled sell amount cannot be positive
                state.sell.amount -= uint256(settledSellAmount.unsafeNeg());
                // If `state.buy.amount()` overflows an `int128`, we'll get a revert inside the pool
                // manager later. We cannot overflow a `uint256`.
                unchecked {
                    state.buy.amount += settledBuyAmount.asCredit(state.buy.token());
                }
            }
        }

        // `data` has been consumed. All that remains is to settle out the net result of all the
        // swaps. Any credit in any token other than `state.buy.token` will be swept to
        // Settler. `state.buy.token` will be sent to `recipient`.
        {
            (IERC20 globalSellToken, uint256 globalSellAmount) = state.globalSell.get();
            uint256 globalBuyAmount = _take(state, notes, recipient, minBuyAmount);
            if (globalSellToken == ETH_ADDRESS) {
                IPoolManager(_operator()).settle{value: globalSellAmount}();
            } else if (feeOnTransfer) {
                // We've already transferred the sell token to the pool manager and
                // `settle`'d. `globalSellAmount` is the verbatim credit in that token stored by the
                // pool manager. We only need to handle the case of incomplete filling.
                if (globalSellAmount != 0) {
                    IPoolManager(_operator()).unsafeTake(
                        globalSellToken, payer == address(this) ? address(this) : _msgSender(), globalSellAmount
                    );
                }
            } else {
                // While `notes` records a credit value, the pool manager actually records a debt
                // for the global sell token. We recover the exact amount of that debt and then pay
                // it.
                // `globalSellAmount` is _usually_ zero, but if it isn't it represents a partial
                // fill. This subtraction recovers the actual debt recorded in the pool manager.
                unchecked {
                    uint256 debt = state.globalSellAmount - globalSellAmount;
                    _pay(globalSellToken, payer, debt, permit, isForwarded, sig);
                }
            }
            return abi.encode(abi.encode(globalBuyAmount));
        }
    }
}

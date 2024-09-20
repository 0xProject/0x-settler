// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {SettlerAbstract} from "../SettlerAbstract.sol";

import {Panic} from "../utils/Panic.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";
import {FreeMemory} from "../utils/FreeMemory.sol";

import {
    TooMuchSlippage,
    DeltaNotPositive,
    DeltaNotNegative,
    ZeroBuyAmount,
    BoughtSellToken,
    TokenHashCollision
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

library IndexAndDeltaLib {
    type IndexAndDelta is uint256;

    uint256 private constant _MASK = 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff;

    function construct(uint256 i, uint256 initAmount) internal pure returns (IndexAndDelta r) {
        assembly ("memory-safe") {
            r := or(shl(0xf8, i), and(_MASK, initAmount))
        }
    }

    function index(IndexAndDelta x) internal pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := shr(0xf8, x)
        }
    }

    function amount(IndexAndDelta x) internal pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := and(_MASK, x)
        }
    }

    function unsafeAdd(IndexAndDelta x, uint256 incr) internal pure returns (IndexAndDelta r) {
        assembly ("memory-safe") {
            r := add(x, incr)
        }
    }

    function unsafeSub(IndexAndDelta x, uint256 decr) internal pure returns (IndexAndDelta r) {
        assembly ("memory-safe") {
            r := sub(x, decr)
        }
    }
}

/// This library is a highly-optimized, enumerable mapping from tokens to deltas. It consists of 3
/// components that must be kept synchronized. There is a transient storage "mapping" that maps
/// token addresses to `memory` pointers (aka `Note memory`). There is a `memory` array of `Note`
/// (aka `Note[] memory`) that has up to `_MAX_TOKENS` pre-allocated. And then there is an implicit
/// heap packed at the end of the array that stores the `Note`s and is prepended with the number of
/// allocated objects. While the length of the `Notes[]` array grows and shrinks as tokens are added
/// and retired, the heap never shrinks and is only deallocated when the context of `unlockCallback`
/// returns. The function `destruct` is used for clearing the transient storage "mapping", but the
/// array itself is perfectly usable afterwards.
library NotesLib {
    using IndexAndDeltaLib for IndexAndDeltaLib.IndexAndDelta;

    uint256 private constant _AMOUNT_MASK = 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff;
    uint256 private constant _ADDRESS_MASK = 0x00ffffffffffffffffffffffffffffffffffffffff;

    /// This is the maximum number of tokens that may be involved in a UniV4 action. If more tokens
    /// than this are involved, then we will Panic with code 0x32 (indicating an out-of-bounds array
    /// access). Increasing or decreasing this value requires no changes elsewhere in this file.
    uint256 private constant _MAX_TOKENS = 8;

    // TODO: swap the fields of this struct; putting `note` first saves a bunch of ADDs
    // TODO: maybe move the `index` to share its slot with `token` instead of `amount`; `amount` is
    //       more frequently modified than `index` and `token` is never modified, so packing the
    //       less-frequently-modified members together means less masking.
    // TODO: store pointers intead of indices in each `note` field
    struct Note {
        IERC20 token;
        IndexAndDeltaLib.IndexAndDelta note;
    }

    type NotePtr is uint256;

    function construct() internal pure returns (Note[] memory r) {
        assembly ("memory-safe") {
            r := mload(0x40)
            let len := add(0x20, shl(0x05, _MAX_TOKENS))
            // zeroize all the memory required to store the notes
            codecopy(r, codesize(), len)
            // allocate memory
            mstore(0x40, add(len, r))
        }
    }

    function eq(Note memory x, Note memory y) internal pure returns (bool r) {
        assembly ("memory-safe") {
            r := eq(x, y)
        }
    }

    function amount(Note memory x) internal pure returns (uint256) {
        return x.note.amount();
    }

    function setAmount(Note memory x, uint256 newAmount) internal pure {
        x.note = IndexAndDeltaLib.construct(x.note.index(), newAmount);
    }

    function get(Note memory x) internal pure returns (IERC20, uint256) {
        return (x.token, x.note.amount());
    }

    function get(Note[] memory a, uint256 i) internal pure returns (IERC20 token, uint256 retAmount) {
        assembly ("memory-safe") {
            let x := mload(add(add(0x20, shl(0x05, i)), a))
            token := mload(x)
            retAmount := and(_AMOUNT_MASK, mload(add(0x20, x)))
        }
    }

    function get(Note[] memory a, IERC20 token, uint256 hashMul, uint256 hashMod) internal pure returns (NotePtr x) {
        assembly ("memory-safe") {
            token := and(_ADDRESS_MASK, token)
            x :=
                add(a, add(add(0x20, shl(0x05, _MAX_TOKENS)), mod(mulmod(token, hashMul, hashMod), shl(0x06, _MAX_TOKENS))))
            let oldToken := mload(x)
            if mul(oldToken, xor(oldToken, token)) { // TODO(dekz): check me on this?
                mstore(0x00, 0x9a62e8b4) // selector for `TokenHashCollision(address,address)`
                mstore(0x20, oldToken)
                mstore(0x40, token)
                revert(0x1c, 0x44)
            }
            mstore(x, token)
        }
    }

    /// This function does *NOT* check whether `x` is already on `a`. If it is, then this will
    /// result in corruption.
    function push(Note[] memory a, Note memory x) internal pure {
        assembly ("memory-safe") {
            let len := add(0x01, mload(a))
            // We don't need to check for out-of-bounds access here, the check in `get` above for
            // token collision handles that for us. It's not possible to `get` more than
            // `_MAX_TOKENS` tokens
            mstore(a, len)
            mstore(add(shl(0x05, len), a), x)

            let note_ptr := add(0x20, x)
            let note := mload(note_ptr)
            note := or(shl(0xf8, len), and(_AMOUNT_MASK, note))
            mstore(note_ptr, note)
        }
    }

    /// This function does *NOT* check that `a` is nonempty. If it is, you will get underflow and
    /// either corruption or an OOG.
    function pop(Note[] memory a) internal pure {
        assembly ("memory-safe") {
            let len := mload(a)
            let end := add(shl(0x05, len), a)

            // Clear the backpointer (index) in the referred-to `Note`
            let i_ptr := add(0x20, mload(end))
            mstore(i_ptr, and(_AMOUNT_MASK, mload(i_ptr)))
            // We do not deallocate the `Note`

            // Decrement the length of `a`
            mstore(a, sub(len, 0x01))
        }
    }

    /// This function does *NOT* check that `x` is on `a`. If it isn't depending on whether `a` is
    /// empty, you may get corruption or an OOG.
    function del(Note[] memory a, Note memory x) internal pure {
        assembly ("memory-safe") {
            // Clear the backpointer (index) in the referred-to `Note`
            let x_note_ptr := add(0x20, x)
            let x_note := mload(x_note_ptr)
            mstore(x_note_ptr, and(_AMOUNT_MASK, x_note))
            let x_ptr := add(and(0x1fe0, shr(0xf3, x_note)), a)
            // We do not deallocate `x`

            // Overwrite the vacated indirection pointer `x_ptr` with the one at the end.
            let len := mload(a)
            let end_ptr := add(shl(0x05, len), a)
            let end := mload(end_ptr)
            mstore(x_ptr, end)

            // Fix up the backpointer (index) in the referred-to `Note` to point to the new
            // location of the indirection pointer.
            let end_note_ptr := add(0x20, end)
            let end_note := mload(end_note_ptr)
            end_note := or(and(not(_AMOUNT_MASK), x_note), and(_AMOUNT_MASK, end_note))
            mstore(end_note_ptr, end_note)

            // Decrement the length of `a`
            mstore(a, sub(len, 0x01))
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

abstract contract UniswapV4 is SettlerAbstract, FreeMemory {
    using SafeTransferLib for IERC20;
    using UnsafeMath for uint256;
    using UnsafeMath for int256;
    using CreditDebt for int256;
    using IndexAndDeltaLib for IndexAndDeltaLib.IndexAndDelta;
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

            mstore(add(0x88, data), hashMod)
            mstore(add(0x78, data), hashMul)
            mstore(add(0x68, data), amountOutMin)
            mstore(add(0x58, data), recipient)
            mstore(add(0x44, data), add(0x4f, pathLen))
            mstore(add(0x24, data), 0x20)
            mstore(add(0x04, data), 0x48c89491) // selector for `unlock(bytes)`
            mstore(data, add(0x93, pathLen))
            mstore8(add(0xa8, data), feeOnTransfer)

            mstore(0x40, add(add(0xd3, data), pathLen))
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

            let ptr := add(0x132, data)
            mcopy(ptr, add(0x20, fills), pathLen)
            ptr := add(ptr, pathLen)
            // TODO: encode sig length in 3 bytes instead of 32
            mcopy(ptr, add(0x20, sig), sigLen)
            ptr := add(ptr, sigLen)
            mstore(ptr, sigLen)
            ptr := add(0x20, ptr)

            mstore(0x40, ptr)

            mstore8(add(0x131, data), isForwarded)
            mcopy(add(0xf1, data), add(0x20, permit), 0x40)
            mcopy(add(0xb1, data), mload(permit), 0x40) // aliases `payer` on purpose
            mstore(add(0x9d, data), 0x00) // payer

            mstore(add(0x88, data), hashMod)
            mstore(add(0x78, data), hashMul)
            mstore(add(0x68, data), amountOutMin)
            mstore(add(0x58, data), recipient)
            mstore(add(0x44, data), add(0x132, add(pathLen, sigLen)))
            mstore(add(0x24, data), 0x20)
            mstore(add(0x04, data), 0x48c89491) // selector for `unlock(bytes)`
            mstore(data, add(0x176, add(pathLen, sigLen)))
            mstore8(add(0xa8, data), feeOnTransfer)
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
    //// it is accounted slightly differently from the other tokens. To avoid doing a linear scan
    //// each time a new token is encountered, the transient storage slot named by each token stores
    //// the pointer to the corresponding `Note` object. The function `_take` is responsible for
    //// iterating over the list of tokens and withdrawing any credit to the appropriate recipient.
    ////
    //// `state` exists to reduce stack pressure and to simplify and gas-optimize the process of
    //// swapping. By keeping track of the sell and buy token on each hop, we're able to compress
    //// the representation of the fills required to satisfy the swap. Most often in a swap, the
    //// tokens in adjacent fills are somewhat in common. By caching, we avoid having them appear
    //// multiple times in the calldata. Additionally, this caching helps us avoid having to
    //// dereference the pointer in transient storage.

    /// Because we have to ABIEncode the arguments to `.swap(...)` and copy the `hookData` from
    /// calldata into memory, we save gas by deallocating at the end of this function.
    function _swap(IPoolManager.PoolKey memory key, IPoolManager.SwapParams memory params, bytes calldata hookData)
        private
        DANGEROUS_freeMemory
        returns (BalanceDelta)
    {
        return IPoolManager(_operator()).swap(key, params, hookData);
    }

    // the mandatory fields are
    // 2 - sell bps
    // 1 - pool key tokens case
    // 3 - pool fee
    // 3 - pool tick spacing
    // 20 - pool hooks
    // 3 - hook data length
    uint256 private constant _HOP_DATA_LENGTH = 32;

    /// Decode a `PoolKey` from its packed representation in `bytes`. Returns the suffix of the
    /// bytes that are not consumed in the decoding process. The first byte of `data` describes
    /// which of the compact representations for the hop is used.
    ///   0 -> sell and buy tokens remain unchanged from the previous fill (pure multiplex)
    ///   1 -> sell token remains unchanged from the previous fill, buy token is read from `data` (diamond multiplex)
    ///   2 -> sell token becomes the buy token from the previous fill, new buy token is read from `data` (multihop)
    ///   3 -> both sell and buy token are read from `data`
    ///
    /// This function is also responsible for calling `NotesLib.insert` (via `StateLib.setSell` and
    /// `StateLib.setBuy`), which maintains the `notes` array and the corresponding mapping in
    /// transient storage
    function _getPoolKey(
        IPoolManager.PoolKey memory key,
        StateLib.State memory state,
        NotesLib.Note[] memory notes,
        bytes calldata data
    ) private pure returns (bool, bytes calldata) {
        uint256 caseKey = uint8(bytes1(data));
        data = data[1:];
        if (caseKey != 0) {
            if (caseKey > 1) {
                if (state.sell.amount() == 0) {
                    if (state.sell.note.index() == notes.length) {
                        // TODO: evaluate whether this is actually more gas efficient
                        notes.pop();
                    } else {
                        notes.del(state.sell);
                    }
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

            IERC20 buyToken = IERC20(address(uint160(bytes20(data))));
            data = data[20:];

            state.setBuy(notes, buyToken);
            if (state.buy.eq(state.globalSell)) {
                revert BoughtSellToken(state.globalSell.token);
            }
        }

        bool zeroForOne = state.sell.token < state.buy.token;
        (key.token0, key.token1) =
            zeroForOne ? (state.sell.token, state.buy.token) : (state.buy.token, state.sell.token);
        key.fee = uint24(bytes3(data));
        data = data[3:];
        key.tickSpacing = int24(uint24(bytes3(data)));
        data = data[3:];
        key.hooks = IHooks.wrap(address(uint160(bytes20(data))));
        data = data[20:];

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
        if (state.buy.note.index() == notes.length) {
            // TODO: evaluate whether this is actually more gas efficient
            notes.pop();
        } else {
            // Guaranteed to exist by the `ZeroBuyAmount` check in the main loop
            notes.del(state.buy);
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
                    IPoolManager(_operator()).unsafeTake(firstNote.token, address(this), firstNote.amount());
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
                if (buyToken == IERC20(address(0))) {
                    buyToken = ETH_ADDRESS;
                }
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
            ISignatureTransfer.SignatureTransferDetails memory transferDetails =
                ISignatureTransfer.SignatureTransferDetails({to: _operator(), requestedAmount: sellAmount});
            _transferFrom(permit, transferDetails, sig, isForwarded);
        }
        return IPoolManager(_operator()).settle();
    }

    function _setup(bytes calldata data, bool feeOnTransfer, uint256 hashMul, uint256 hashMod, address payer)
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
            if (sellToken == ETH_ADDRESS) {
                sellToken = IERC20(address(0));
            }
            notes = state.construct(sellToken, hashMul, hashMod);
        }

        // This assembly block is just here to appease the compiler. We only use `permit` and `sig`
        // in the codepaths where they are set away from the values initialized here.
        assembly ("memory-safe") {
            permit := calldatasize()
            sig.offset := calldatasize()
            sig.length := 0x00
        }

        if (state.globalSell.token == IERC20(address(0))) {
            assert(payer == address(this));
            data = data[20:];

            uint16 bps = uint16(bytes2(data));
            data = data[2:];
            unchecked {
                state.globalSell.setAmount((address(this).balance * bps).unsafeDiv(BASIS));
            }
        } else {
            if (payer == address(this)) {
                data = data[20:];

                uint16 bps = uint16(bytes2(data));
                data = data[2:];
                unchecked {
                    state.globalSell.setAmount((state.globalSell.token.balanceOf(address(this)) * bps).unsafeDiv(BASIS));
                }
            } else {
                assert(payer == address(0));

                assembly ("memory-safe") {
                    // this is super dirty, but it works because although `permit` is aliasing in
                    // the middle of `payer`, because `payer` is all zeroes, it's treated as padding
                    // for the first word of `permit`, which is the sell token
                    permit := sub(data.offset, 0x0c)
                    isForwarded := and(0x01, calldataload(add(0x55, data.offset)))

                    // `sig` is packed at the end of `data`, in "reverse ABIEncoded" fashion
                    sig.offset := sub(add(data.offset, data.length), 0x20)
                    // TODO: encode sig as 3 bytes instead of 32
                    sig.length := calldataload(sig.offset)
                    sig.offset := sub(sig.offset, sig.length)

                    // Remove `permit` and `isForwarded` from the front of `data`
                    data.offset := add(0x75, data.offset)
                    // Remove `sig` from the back of `data`
                    data.length := sub(sub(data.length, 0x95), sig.length)
                }

                state.globalSell.setAmount(_permitToSellAmountCalldata(permit));
            }

            if (feeOnTransfer) {
                state.globalSell.setAmount(
                    _pay(state.globalSell.token, payer, state.globalSell.amount(), permit, isForwarded, sig)
                );
            }
        }

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

        // Set up `state` and `notes`. The other values are ancillary and may be used when we need
        // to settle any debt at the end of swapping.
        (
            bytes calldata newData,
            StateLib.State memory state,
            NotesLib.Note[] memory notes,
            ISignatureTransfer.PermitTransferFrom calldata permit,
            bool isForwarded,
            bytes calldata sig
        ) = _setup(data, feeOnTransfer, hashMul, hashMod, payer);
        data = newData;

        // Now that we've unpacked and decoded the header, we can begin decoding the array of swaps
        // and executing them.
        IPoolManager.PoolKey memory key;
        IPoolManager.SwapParams memory params;
        while (data.length >= _HOP_DATA_LENGTH) {
            uint16 bps = uint16(bytes2(data));
            data = data[2:];

            bool zeroForOne;
            (zeroForOne, data) = _getPoolKey(key, state, notes, data);
            bytes calldata hookData;
            (hookData, data) = _getHookData(data);

            params.zeroForOne = zeroForOne;
            unchecked {
                params.amountSpecified = int256((state.sell.amount() * bps).unsafeDiv(BASIS)).unsafeNeg();
            }
            // TODO: price limits
            params.sqrtPriceLimitX96 = zeroForOne ? 4295128740 : 1461446703485210103287273052203988822378723970341;

            BalanceDelta delta = _swap(key, params, hookData);
            {
                (int256 settledSellAmount, int256 settledBuyAmount) =
                    zeroForOne ? (delta.amount0(), delta.amount1()) : (delta.amount1(), delta.amount0());
                // some insane hooks may increase the sell amount; obviously this may result in
                // unavoidable reverts in some cases. but we still need to make sure that we don't
                // underflow to avoid wildly unexpected behavior
                {
                    IndexAndDeltaLib.IndexAndDelta note = state.sell.note;
                    // The pool manager enforces that the settled sell amount cannot be positive
                    uint256 settledSellDebt = uint256(settledSellAmount.unsafeNeg());
                    if (note.amount() < settledSellDebt) {
                        Panic.panic(Panic.ARITHMETIC_OVERFLOW);
                    }
                    state.sell.note = note.unsafeSub(settledSellDebt);
                }
                if (settledBuyAmount == 0) {
                    revert ZeroBuyAmount(state.buy.token);
                }
                // if `state.buy.amount()` overflows an `int128`, we'll get a revert inside the pool
                // manager later
                state.buy.note = state.buy.note.unsafeAdd(settledBuyAmount.asCredit(state.buy.token));
            }
        }

        // `data` has been consumed. All that remains is to settle out the net result of all the
        // swaps. Any credit in any token other than `state.buy.token` will be swept to
        // Settler. `state.buy.token` will be sent to `recipient`.
        {
            (IERC20 globalSellToken, uint256 globalSellAmount) = state.globalSell.get();
            uint256 globalBuyAmount = _take(state, notes, recipient, minBuyAmount);
            if (globalSellToken == IERC20(address(0))) {
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
            return abi.encode(globalBuyAmount);
        }
    }
}

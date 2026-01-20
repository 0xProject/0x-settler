// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";

import {Panic} from "../utils/Panic.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";
import {FastLogic} from "../utils/FastLogic.sol";

import {revertTooMuchSlippage, BoughtSellToken, DeltaNotPositive, DeltaNotNegative} from "./SettlerErrors.sol";

library CreditDebt {
    using UnsafeMath for int256;

    function asCredit(int256 delta, NotePtr note) internal pure returns (uint256) {
        if (delta < 0) {
            assembly ("memory-safe") {
                mstore(note, 0x4c085bf1) // selector for `DeltaNotPositive(address)`; clobbers `note.amount()`
                revert(add(0x1c, note), 0x24)
            }
        }
        return uint256(delta);
    }

    function asDebt(int256 delta, NotePtr note) internal pure returns (uint256) {
        if (delta > 0) {
            assembly ("memory-safe") {
                mstore(note, 0x3351b260) // selector for `DeltaNotNegative(address)`; clobbers `note.amount()`
                revert(add(0x1c, note), 0x24)
            }
        }
        return uint256(delta.unsafeNeg());
    }
}

/// This type is the same as `NotesLib.Note`, but as a user-defined value type to sidestep solc's
/// awful memory handling.
type NotePtr is uint256;

/// This library is a highly-optimized, in-memory, enumerable mapping from tokens to amounts. It
/// consists of 2 components that must be kept synchronized. There is a `memory` array of `Note`
/// (aka `Note[] memory`) that has up to `MAX_TOKENS` pre-allocated. And there is an implicit heap
/// packed at the end of the array that stores the `Note`s. Each `Note` has a backpointer that knows
/// its location in the `Notes[] memory`. While the length of the `Notes[]` array grows and shrinks
/// as tokens are added and retired, heap objects are only cleared/deallocated when the context
/// returns. Looking up the `Note` object corresponding to a token uses the perfect hash formed by
/// `hashMul` and `hashMod`. Pay special attention to these parameters. See further below for
/// recommendations on how to select values for them. A hash collision will result in a revert with
/// signature `TokenHashCollision(address,address)`.
library NotesLib {
    uint256 private constant _ADDRESS_MASK = 0x00ffffffffffffffffffffffffffffffffffffffff;
    address internal constant ETH_ADDRESS = 0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE;

    /// This is the maximum number of tokens that may be involved in an action. Increasing or
    /// decreasing this value requires no other changes elsewhere in this file.
    uint256 internal constant MAX_TOKENS = 8;

    type NotePtrPtr is uint256;

    struct Note {
        uint256 amount;
        IERC20 token;
        NotePtrPtr backPtr;
    }

    function construct() internal pure returns (Note[] memory r) {
        assembly ("memory-safe") {
            r := mload(0x40)
            // set the length of `r` to zero
            mstore(r, 0x00)
            // zeroize the heap
            codecopy(add(add(0x20, shl(0x05, MAX_TOKENS)), r), codesize(), mul(0x60, MAX_TOKENS))
            // allocate memory
            mstore(0x40, add(add(0x20, shl(0x07, MAX_TOKENS)), r))
        }
    }

    function amount(NotePtr note) internal pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := mload(note)
        }
    }

    function setAmount(NotePtr note, uint256 newAmount) internal pure {
        assembly ("memory-safe") {
            mstore(note, newAmount)
        }
    }

    function token(NotePtr note) internal pure returns (IERC20 r) {
        assembly ("memory-safe") {
            r := mload(add(0x20, note))
        }
    }

    function tokenIsEth(NotePtr note) internal pure returns (bool r) {
        assembly ("memory-safe") {
            r := eq(ETH_ADDRESS, mload(add(0x20, note)))
        }
    }

    function eq(Note memory x, Note memory y) internal pure returns (bool) {
        NotePtr yp;
        assembly ("memory-safe") {
            yp := y
        }
        return eq(x, yp);
    }

    function eq(Note memory x, NotePtr y) internal pure returns (bool) {
        NotePtr xp;
        assembly ("memory-safe") {
            xp := x
        }
        return eq(xp, y);
    }

    function eq(NotePtr x, NotePtr y) internal pure returns (bool r) {
        assembly ("memory-safe") {
            r := eq(x, y)
        }
    }

    function unsafeGet(Note[] memory a, uint256 i) internal pure returns (IERC20 retToken, uint256 retAmount) {
        assembly ("memory-safe") {
            let x := mload(add(add(0x20, shl(0x05, i)), a))
            retToken := mload(add(0x20, x))
            retAmount := mload(x)
        }
    }

    //// How to generate a perfect hash:
    ////
    //// The arguments `hashMul` and `hashMod` are required to form a perfect hash for a table with
    //// size `NotesLib.MAX_TOKENS` when applied to all the tokens involved in fills. The hash
    //// function is constructed as `uint256 hash = mulmod(uint256(uint160(address(token))),
    //// hashMul, hashMod) % NotesLib.MAX_TOKENS`.
    ////
    //// The "simple" or "obvious" way to do this is to simply try random 128-bit numbers for both
    //// `hashMul` and `hashMod` until you obtain a function that has no collisions when applied to
    //// the tokens involved in fills. A substantially more optimized algorithm can be obtained by
    //// selecting several (at least 10) prime values for `hashMod`, precomputing the limb moduluses
    //// for each value, and then selecting randomly from among them. The author recommends using
    //// the 10 largest 64-bit prime numbers: 2^64 - {59, 83, 95, 179, 189, 257, 279, 323, 353,
    //// 363}. `hashMul` can then be selected randomly or via some other optimized method.
    ////
    //// Note that in spite of the fact that some AMMs represent Ether (or the native asset of the
    //// chain) as `address(0)`, we represent Ether as `SettlerAbstract.ETH_ADDRESS` (the address of
    //// all `e`s) for homogeneity with other parts of the codebase, and because the decision to
    //// represent Ether as `address(0)` was stupid in the first place. `address(0)` represents the
    //// absence of a thing, not a special case of the thing. It creates confusion with
    //// uninitialized memory, storage, and variables.
    function get(Note[] memory a, IERC20 newToken, uint256 hashMul, uint256 hashMod)
        internal
        pure
        returns (NotePtr x)
    {
        assembly ("memory-safe") {
            newToken := and(_ADDRESS_MASK, newToken)
            x := add(add(0x20, shl(0x05, MAX_TOKENS)), a) // `x` now points at the first `Note` on the heap
            x := add(mod(mulmod(newToken, hashMul, hashMod), mul(0x60, MAX_TOKENS)), x) // combine with token hash
            // `x` now points at the exact `Note` object we want; let's check it to be sure, though
            let x_token_ptr := add(0x20, x)

            // check that we haven't encountered a hash collision. checking for a hash collision is
            // equivalent to checking for array out-of-bounds or overflow.
            {
                let old_token := mload(x_token_ptr)
                if mul(or(mload(add(0x40, x)), old_token), xor(old_token, newToken)) {
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

            // initialize the token (possibly redundant)
            mstore(x_token_ptr, newToken)
        }
    }

    function add(Note[] memory a, Note memory x) internal pure {
        NotePtr xp;
        assembly ("memory-safe") {
            xp := x
        }
        return add(a, xp);
    }

    function add(Note[] memory a, NotePtr x) internal pure {
        assembly ("memory-safe") {
            let backptr_ptr := add(0x40, x)
            let backptr := mload(backptr_ptr)
            if iszero(backptr) {
                let len := add(0x01, mload(a))
                // We don't need to check for overflow or out-of-bounds access here; the checks in
                // `get` above for token collision handle that for us. It's not possible to `get`
                // more than `MAX_TOKENS` tokens
                mstore(a, len)
                backptr := add(shl(0x05, len), a)
                mstore(backptr, x)
                mstore(backptr_ptr, backptr)
            }
        }
    }

    function del(Note[] memory a, Note memory x) internal pure {
        NotePtr xp;
        assembly ("memory-safe") {
            xp := x
        }
        return del(a, xp);
    }

    function del(Note[] memory a, NotePtr x) internal pure {
        assembly ("memory-safe") {
            let x_backptr_ptr := add(0x40, x)
            let x_backptr := mload(x_backptr_ptr)
            if x_backptr {
                // Clear the backpointer in the referred-to `Note`
                mstore(x_backptr_ptr, 0x00)
                // We do not deallocate `x`

                // Decrement the length of `a`
                let len := mload(a)
                mstore(a, sub(len, 0x01))

                // Check if this is a "swap and pop" or just a "pop"
                let end_ptr := add(shl(0x05, len), a)
                if iszero(eq(end_ptr, x_backptr)) {
                    // Overwrite the vacated indirection pointer `x_backptr` with the value at the end.
                    let end := mload(end_ptr)
                    mstore(x_backptr, end)

                    // Fix up the backpointer in `end` to point to the new location of the indirection
                    // pointer.
                    let end_backptr_ptr := add(0x40, end)
                    mstore(end_backptr_ptr, x_backptr)
                }
            }
        }
    }
}

using NotesLib for NotePtr global;

/// `State` behaves as if it were declared as:
///     struct State {
///         NotesLib.Note buy;
///         NotesLib.Note sell;
///         NotesLib.Note globalSell;
///         uint256 globalSellAmount;
///         uint256 _hashMul;
///         uint256 _hashMod;
///     }
/// but we use a user-defined value type because solc generates very gas-inefficient boilerplate
/// that allocates and zeroes a bunch of memory. Consequently, everything is written in assembly and
/// accessors are provided for the relevant members.
type State is bytes32;

library StateLib {
    using NotesLib for NotesLib.Note;
    using NotesLib for NotesLib.Note[];

    function construct(IERC20 token, uint256 hashMul, uint256 hashMod)
        internal
        pure
        returns (State state, NotesLib.Note[] memory notes)
    {
        assembly ("memory-safe") {
            // Allocate memory
            state := mload(0x40)
            mstore(0x40, add(0xc0, state))
        }
        // All the pointers in `state` are now pointing into unallocated memory
        notes = NotesLib.construct();
        // The pointers in `state` are now illegally aliasing elements in `notes`
        NotePtr notePtr = notes.get(token, hashMul, hashMod);

        // Here we actually set the pointers into a legal area of memory
        setBuy(state, notePtr);
        setSell(state, notePtr);
        assembly ("memory-safe") {
            // Set `state.globalSell`
            mstore(add(0x40, state), notePtr)
            // Set `state._hashMul`
            mstore(add(0x80, state), hashMul)
            // Set `state._hashMod`
            mstore(add(0xa0, state), hashMod)
        }
    }

    function buy(State state) internal pure returns (NotePtr note) {
        assembly ("memory-safe") {
            note := mload(state)
        }
    }

    function sell(State state) internal pure returns (NotePtr note) {
        assembly ("memory-safe") {
            note := mload(add(0x20, state))
        }
    }

    function globalSell(State state) internal pure returns (NotePtr note) {
        assembly ("memory-safe") {
            note := mload(add(0x40, state))
        }
    }

    function globalSellAmount(State state) internal pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := mload(add(0x60, state))
        }
    }

    function setGlobalSellAmount(State state, uint256 newGlobalSellAmount) internal pure {
        assembly ("memory-safe") {
            mstore(add(0x60, state), newGlobalSellAmount)
        }
    }

    function _hashMul(State state) private pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := mload(add(0x80, state))
        }
    }

    function _hashMod(State state) private pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := mload(add(0xa0, state))
        }
    }

    function checkZeroSellAmount(State state) internal pure {
        NotePtr globalSell_ = state.globalSell();
        if (globalSell_.amount() == 0) {
            assembly ("memory-safe") {
                mstore(globalSell_, 0xfb772a88) // selector for `ZeroSellAmount(address)`; clobbers `globalSell_.amount()`
                revert(add(0x1c, globalSell_), 0x24)
            }
        }
    }

    function setSell(State state, NotePtr notePtr) internal pure {
        assembly ("memory-safe") {
            mstore(add(0x20, state), notePtr)
        }
    }

    function setSell(State state, NotesLib.Note[] memory notes, IERC20 token) internal pure {
        setSell(state, notes.get(token, _hashMul(state), _hashMod(state)));
    }

    function setBuy(State state, NotePtr notePtr) internal pure {
        assembly ("memory-safe") {
            mstore(state, notePtr)
        }
    }

    function setBuy(State state, NotesLib.Note[] memory notes, IERC20 token) internal pure {
        setBuy(state, notes.get(token, _hashMul(state), _hashMod(state)));
    }
}

using StateLib for State global;

library Encoder {
    using FastLogic for bool;

    uint256 internal constant BASIS = 10_000;

    function encode(
        uint256 unlockSelector,
        address recipient,
        IERC20 sellToken,
        uint256 bps,
        bool feeOnTransfer,
        uint256 hashMul,
        uint256 hashMod,
        bytes memory fills,
        uint256 amountOutMin
    ) internal view returns (bytes memory data) {
        hashMul *= 96;
        hashMod *= 96;
        if ((bps > BASIS).or(amountOutMin >> 128 != 0).or(hashMul >> 128 != 0).or(hashMod >> 128 != 0)) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }
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
            mstore(add(0x04, data), unlockSelector)
            mstore(data, add(0xb3, pathLen))
            mstore8(add(0xa8, data), feeOnTransfer)

            mstore(0x40, add(data, add(0xd3, pathLen)))
        }
    }

    function encodeVIP(
        uint256 unlockSelector,
        address recipient,
        bool feeOnTransfer,
        uint256 hashMul,
        uint256 hashMod,
        bytes memory fills,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes memory sig,
        bool isForwarded,
        uint256 amountOutMin
    ) internal pure returns (bytes memory data) {
        hashMul *= 96;
        hashMod *= 96;
        if ((amountOutMin >> 128 != 0).or(hashMul >> 128 != 0).or(hashMod >> 128 != 0)) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }
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
            mstore(add(0x04, data), unlockSelector)
            mstore(data, add(0x115, add(pathLen, sigLen)))

            mstore8(add(0xa8, data), feeOnTransfer)
        }
    }
}

library Decoder {
    using SafeTransferLib for IERC20;
    using UnsafeMath for uint256;
    using NotesLib for NotesLib.Note;
    using NotesLib for NotesLib.Note[];

    uint256 internal constant BASIS = 10_000;

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
    function updateState(State state, NotesLib.Note[] memory notes, bytes calldata data)
        internal
        pure
        returns (bytes calldata)
    {
        bytes32 dataWord;
        assembly ("memory-safe") {
            dataWord := calldataload(data.offset)
        }
        uint256 dataConsumed = 1;

        uint256 caseKey = uint256(dataWord) >> 248;
        if (caseKey != 0) {
            notes.add(state.buy());

            if (caseKey > 1) {
                if (state.sell().amount() == 0) {
                    notes.del(state.sell());
                }
                if (caseKey == 2) {
                    state.setSell(state.buy());
                } else {
                    assert(caseKey == 3);

                    IERC20 sellToken = IERC20(address(uint160(uint256(dataWord) >> 88)));
                    assembly ("memory-safe") {
                        dataWord := calldataload(add(0x14, data.offset))
                    }
                    unchecked {
                        dataConsumed += 20;
                    }

                    state.setSell(notes, sellToken);
                }
            }

            IERC20 buyToken = IERC20(address(uint160(uint256(dataWord) >> 88)));
            unchecked {
                dataConsumed += 20;
            }

            state.setBuy(notes, buyToken);
            if (state.buy().eq(state.globalSell())) {
                assembly ("memory-safe") {
                    let ptr := mload(add(0x40, state)) // dereference `state.globalSell`
                    mstore(ptr, 0x784cb7b8) // selector for `BoughtSellToken(address)`; clobbers `state.globalSell.amount`
                    revert(add(0x1c, ptr), 0x24)
                }
            }
        }

        assembly ("memory-safe") {
            data.offset := add(dataConsumed, data.offset)
            data.length := sub(data.length, dataConsumed)
            // we don't check for array out-of-bounds here; we will check it later in `_getHookData`
        }

        return data;
    }

    function overflowCheck(bytes calldata data) internal pure {
        if (data.length > 16777215) {
            Panic.panic(Panic.ARRAY_OUT_OF_BOUNDS);
        }
    }

    /// Decode an ABI-ish encoded `bytes` from `data`. It is "-ish" in the sense that the encoding
    /// of the length doesn't take up an entire word. The length is encoded as only 3 bytes (2^24
    /// bytes of calldata consumes ~67M gas, much more than the block limit). The payload is also
    /// unpadded. The next fill's `bps` is encoded immediately after the `hookData` payload.
    function decodeBytes(bytes calldata data) internal pure returns (bytes calldata retData, bytes calldata hookData) {
        assembly ("memory-safe") {
            hookData.length := shr(0xe8, calldataload(data.offset))
            hookData.offset := add(0x03, data.offset)
            let hop := add(0x03, hookData.length)

            retData.offset := add(data.offset, hop)
            retData.length := sub(data.length, hop)
        }
    }

    function decodeHeader(bytes calldata data)
        internal
        pure
        returns (
            bytes calldata newData,
            // These values are user-supplied
            address recipient,
            uint256 minBuyAmount,
            uint256 hashMul,
            uint256 hashMod,
            bool feeOnTransfer,
            // `payer` is special and is authenticated
            address payer
        )
    {
        // These values are user-supplied
        assembly ("memory-safe") {
            recipient := shr(0x60, calldataload(data.offset))
            let packed := calldataload(add(0x14, data.offset))
            minBuyAmount := shr(0x80, packed)
            hashMul := and(0xffffffffffffffffffffffffffffffff, packed)
            packed := calldataload(add(0x34, data.offset))
            hashMod := shr(0x80, packed)
            feeOnTransfer := lt(0x00, and(0x1000000000000000000000000000000, packed))

            data.offset := add(0x45, data.offset)
            data.length := sub(data.length, 0x45)
            // we don't check for array out-of-bounds here; we will check it later in `initialize`
        }

        // `payer` is special and is authenticated
        assembly ("memory-safe") {
            payer := shr(0x60, calldataload(data.offset))

            data.offset := add(0x14, data.offset)
            data.length := sub(data.length, 0x14)
            // we don't check for array out-of-bounds here; we will check it later in `initialize`
        }

        newData = data;
    }

    function initialize(bytes calldata data, uint256 hashMul, uint256 hashMod, address payer)
        internal
        view
        returns (
            bytes calldata newData,
            State state,
            NotesLib.Note[] memory notes,
            ISignatureTransfer.PermitTransferFrom calldata permit,
            bool isForwarded,
            bytes calldata sig
        )
    {
        {
            IERC20 sellToken;
            assembly ("memory-safe") {
                sellToken := shr(0x60, calldataload(data.offset))
            }
            // We don't advance `data` here because there's a special interaction between `payer`
            // (which is the 20 bytes in calldata immediately before `data`), `sellToken`, and
            // `permit` that's handled below.
            (state, notes) = StateLib.construct(sellToken, hashMul, hashMod);
        }

        // This assembly block is just here to appease the compiler. We only use `permit` and `sig`
        // in the codepaths where they are set away from the values initialized here.
        assembly ("memory-safe") {
            permit := calldatasize()
            sig.offset := calldatasize()
            sig.length := 0x00
        }

        if (state.globalSell().tokenIsEth()) {
            assert(payer == address(this));

            uint16 bps;
            assembly ("memory-safe") {
                // `data` hasn't been advanced from decoding `sellToken` above. so we have to
                // implicitly advance it by 20 bytes to decode `bps` then advance by 22 bytes

                bps := shr(0x50, calldataload(data.offset))

                data.offset := add(0x16, data.offset)
                data.length := sub(data.length, 0x16)
                // We check for array out-of-bounds below
            }

            unchecked {
                state.globalSell().setAmount((address(this).balance * bps).unsafeDiv(BASIS));
            }
        } else {
            if (payer == address(this)) {
                uint16 bps;
                assembly ("memory-safe") {
                    // `data` hasn't been advanced from decoding `sellToken` above. so we have to
                    // implicitly advance it by 20 bytes to decode `bps` then advance by 22 bytes

                    bps := shr(0x50, calldataload(data.offset))

                    data.offset := add(0x16, data.offset)
                    data.length := sub(data.length, 0x16)
                    // We check for array out-of-bounds below
                }

                unchecked {
                    NotePtr globalSell = state.globalSell();
                    globalSell.setAmount((globalSell.token().fastBalanceOf(address(this)) * bps).unsafeDiv(BASIS));
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
                    // We check for array out-of-bounds below
                }
            }
        }

        Decoder.overflowCheck(data);
        newData = data;
    }
}

library Take {
    using UnsafeMath for uint256;
    using NotesLib for NotesLib.Note;
    using NotesLib for NotesLib.Note[];

    function _callSelector(uint256 selector, IERC20 token, address to, uint256 amount) internal {
        assembly ("memory-safe") {
            token := shl(0x60, token)
            if iszero(amount) {
                mstore(0x20, token)
                mstore(0x00, 0xcbf0dbf5000000000000000000000000) // selector for `ZeroBuyAmount(address)` with `token`'s padding
                revert(0x10, 0x24)
            }

            // save the free memory pointer because we're about to clobber it
            let ptr := mload(0x40)

            mstore(0x60, amount)
            mstore(0x40, to)
            mstore(
                0x2c, mul(iszero(eq(0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee000000000000000000000000, token)), token)
            ) // clears `to`'s padding
            mstore(0x0c, shl(0x60, selector)) // clears `token`'s padding

            if iszero(call(gas(), caller(), 0x00, 0x1c, 0x64, 0x00, 0x00)) {
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }

            // restore clobbered slots
            mstore(0x60, 0x00)
            mstore(0x40, ptr)
        }
    }

    /// `take` is responsible for removing the accumulated credit in each token from the vault. The
    /// current `state.buy` is the global buy token. We return the settled amount of that token
    /// (`buyAmount`), after checking it against the slippage limit (`minBuyAmount`). Each token
    /// with credit causes a corresponding call to `msg.sender.<selector>(token, recipient,
    /// amount)`.
    function take(State state, NotesLib.Note[] memory notes, uint32 selector, address recipient, uint256 minBuyAmount)
        internal
        returns (uint256 buyAmount)
    {
        // NOTICE: Any changes done in this function most likely need to be applied to `CompactTake.take` 
        // as well because it is a copy of this one with a different `_callSelector` function
        notes.del(state.buy());
        if (state.sell().amount() == 0) {
            notes.del(state.sell());
        }

        uint256 length = notes.length;
        // `length` of zero implies that we fully liquidated the global sell token (there is no
        // `amount` remaining) and that the only token in which we have credit is the global buy
        // token. We're about to `take` that token below.
        if (length != 0) {
            {
                NotesLib.Note memory firstNote = notes[0]; // out-of-bounds is impossible
                if (!firstNote.eq(state.globalSell())) {
                    // The global sell token being in a position other than the 1st would imply that
                    // at some point we _bought_ that token. This is illegal and results in a revert
                    // with reason `BoughtSellToken(address)`.
                    _callSelector(selector, firstNote.token, address(this), firstNote.amount);
                }
            }
            for (uint256 i = 1; i < length; i = i.unsafeInc()) {
                (IERC20 token, uint256 amount) = notes.unsafeGet(i);
                _callSelector(selector, token, address(this), amount);
            }
        }

        // The final token to be bought is considered the global buy token. We bypass `notes` and
        // read it directly from `state`. Check the slippage limit. Transfer to the recipient.
        {
            IERC20 buyToken = state.buy().token();
            buyAmount = state.buy().amount();
            if (buyAmount < minBuyAmount) {
                revertTooMuchSlippage(buyToken, minBuyAmount, buyAmount);
            }
            _callSelector(selector, buyToken, recipient, buyAmount);
        }
    }
}

library CompactTake {
    // NOTICE: This library is a copy of `Take` with a different `_callSelector` function
    using UnsafeMath for uint256;
    using NotesLib for NotesLib.Note;
    using NotesLib for NotesLib.Note[];

    function _callSelector(uint256 selector, IERC20 token, address to, uint256 amount) internal {
        assembly ("memory-safe") {
            if iszero(amount) {
                mstore(0x14, token)
                mstore(0x00, 0xcbf0dbf5000000000000000000000000) // selector for `ZeroBuyAmount(address)` with `token`'s padding
                revert(0x10, 0x24)
            }

            // save the free memory pointer because we're about to clobber it
            let ptr := mload(0x40)

            mstore(0x38, amount)
            mstore(0x28, to)
            mstore(
                0x14, mul(lt(0x00, shl(0x60, xor(0x000000000000000000000000eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee, token))), token)
            )
            mstore(0x00, selector) 

            if iszero(call(gas(), caller(), 0x00, 0x1c, 0x3c, 0x00, 0x00)) {
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }

            // restore clobbered slots
            mstore(0x40, ptr)
        }
    }

    /// `take` is responsible for removing the accumulated credit in each token from the vault. The
    /// current `state.buy` is the global buy token. We return the settled amount of that token
    /// (`buyAmount`), after checking it against the slippage limit (`minBuyAmount`). Each token
    /// with credit causes a corresponding call to `msg.sender.<selector>(token, recipient,
    /// amount)`.
    function take(State state, NotesLib.Note[] memory notes, uint32 selector, address recipient, uint256 minBuyAmount)
        internal
        returns (uint256 buyAmount)
    {
        // NOTICE: Any changes done in this function most likely need to be applied to `Take.take` 
        // as well because this function is a copy of it with a different `_callSelector` function
        notes.del(state.buy());
        if (state.sell().amount() == 0) {
            notes.del(state.sell());
        }

        uint256 length = notes.length;
        // `length` of zero implies that we fully liquidated the global sell token (there is no
        // `amount` remaining) and that the only token in which we have credit is the global buy
        // token. We're about to `take` that token below.
        if (length != 0) {
            {
                NotesLib.Note memory firstNote = notes[0]; // out-of-bounds is impossible
                if (!firstNote.eq(state.globalSell())) {
                    // The global sell token being in a position other than the 1st would imply that
                    // at some point we _bought_ that token. This is illegal and results in a revert
                    // with reason `BoughtSellToken(address)`.
                    _callSelector(selector, firstNote.token, address(this), firstNote.amount);
                }
            }
            for (uint256 i = 1; i < length; i = i.unsafeInc()) {
                (IERC20 token, uint256 amount) = notes.unsafeGet(i);
                _callSelector(selector, token, address(this), amount);
            }
        }

        // The final token to be bought is considered the global buy token. We bypass `notes` and
        // read it directly from `state`. Check the slippage limit. Transfer to the recipient.
        {
            IERC20 buyToken = state.buy().token();
            buyAmount = state.buy().amount();
            if (buyAmount < minBuyAmount) {
                revertTooMuchSlippage(buyToken, minBuyAmount, buyAmount);
            }
            _callSelector(selector, buyToken, recipient, buyAmount);
        }
    }
}

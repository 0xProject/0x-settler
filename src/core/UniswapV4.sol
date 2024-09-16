// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {SettlerAbstract} from "../SettlerAbstract.sol";

import {Panic} from "../utils/Panic.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";
import {FreeMemory} from "../utils/FreeMemory.sol";

import {TooMuchSlippage, DeltaNotPositive, DeltaNotNegative} from "./SettlerErrors.sol";

import {PoolKey, BalanceDelta, IHooks, IPoolManager, UnsafePoolManager, POOL_MANAGER, IUnlockCallback} from "./UniswapV4Types.sol";

library UnsafeArray {
    function unsafeGet(UniswapV4.TokenDelta[] memory a, uint256 i)
        internal
        pure
        returns (IERC20 token, int256 creditDebt)
    {
        assembly ("memory-safe") {
            let r := mload(add(a, add(0x20, shl(0x05, i))))
            token := mload(r)
            creditDebt := mload(add(0x20, r))
        }
    }
}

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

type IndexAndDelta is bytes32;

library IndexAndDeltaAccessors {
    function index(IndexAndDelta x) internal pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := shr(0xf8, x)
        }
    }

    function delta(IndexAndDelta x) internal pure returns (int256 r) {
        assembly ("memory-safe") {
            r := signextend(0x1f, x)
        }
    }
}

using IndexAndDeltaAccessors for IndexAndDelta global;

/// This library is a highly-optimized, enumerable mapping from tokens to deltas
library NotedTokens {
    /// This is the maximum number of tokens that may be involved in a UniV4 action. If more tokens
    /// than this are involved, then we will Panic with code 0x32 (indicating an out-of-bounds array
    /// access).
    uint256 private constant _MAX_TOKENS = 8;

    struct TokenNote {
        IERC20 token;
        IndexAndDelta note;
    }

    function construct() internal pure returns (TokenNote[] memory r) {
        assembly ("memory-safe") {
            r := mload(0x40)
            mstore(r, 0x00)
            mstore(add(r, add(0x20, shl(0x05, _MAX_TOKENS))), 0x00)
            mstore(0x40, add(add(0x40, mul(_MAX_TOKENS, 0x60)), r))
        }
    }

    function get(TokenNote[] memory a, uint256 i) internal pure returns (IERC20 token, int256 delta) {
        assembly ("memory-safe") {
            let x := mload(add(add(0x20, shl(0x05, i)), a))
            token := mload(x)
            delta := signextend(0x1f, mload(add(0x20, x)))
        }
    }

    function get(TokenNote[] memory, IERC20 token) internal view returns (int256 delta) {
        assembly ("memory-safe") {
            delta := signextend(0x1f, mload(add(0x20, tload(and(0xffffffffffffffffffffffffffffffffffffffff, token)))))
        }
    }

    // TODO: store pointers intead of indices in each `note` field

    /// It is an error to `push` a token that is already in `a`. This is not checked and does not
    /// throw.
    function push(TokenNote[] memory a, IERC20 token) internal returns (TokenNote memory r) {
        assembly ("memory-safe") {
            // TODO: remove this check; it's always true
            if iszero(eq(mload(0x40), sub(r, 0x40))) {
                revert(0x00, 0x00)
            }
            mstore(0x40, sub(r, 0x40)) // solc is fucking stupid

            token := and(0xffffffffffffffffffffffffffffffffffffffff, token)

            // Increment the length of `a`
            let i := add(0x01, mload(a))
            mstore(a, i)
            // `i` is now 1-indexed

            // Find the first free `TokenNote` object (in memory after `a`)
            let indirectArrayEnd := add(add(0x20, shl(0x05, _MAX_TOKENS)), a)
            let noteAllocations := mload(indirectArrayEnd)
            r := add(indirectArrayEnd, add(0x20, shl(0x06, noteAllocations)))
            // Allocate it
            mstore(indirectArrayEnd, add(0x01, noteAllocations))

            // Set the indirection pointer stored in `a` at the appropriate index to `r`
            mstore(add(add(0x20, a), shl(0x05, i)), r)

            // Set the transient storage mapping for `token` to point at `r`
            tstore(token, r)

            // Initialize `r`
            mstore(r, token)
            mstore(add(0x20, r), shl(0xf8, i))
        }
    }

    function getDefault(TokenNote[] memory a, IERC20 token) internal returns (int256 delta) {
        assembly ("memory-safe") {
            token := and(0xffffffffffffffffffffffffffffffffffffffff, token)
            let x := tload(token)
            switch x
            case 0 {
                // Increment the length of `a`
                let i := add(0x01, mload(a))
                mstore(a, i)
                // `i` is now 1-indexed; we do not require bounds-checking on `i` because it is
                // implicitly bounded above by `noteAllocations`, which is bounds-checked

                // Find the first free `TokenNote` object (in memory after `a`)
                let indirectArrayEnd := add(add(0x20, shl(0x05, _MAX_TOKENS)), a)
                let noteAllocations := mload(indirectArrayEnd)
                if eq(noteAllocations, _MAX_TOKENS) {
                    mstore(0x00, 0x4e487b71) // selector for `Panic(uint256)`
                    mstore(0x20, 0x32) // array out of bounds
                    revert(0x1c, 0x24)
                }
                x := add(indirectArrayEnd, add(0x20, shl(0x06, noteAllocations)))
                // Allocate it
                mstore(indirectArrayEnd, add(0x01, noteAllocations))

                // Set the indirection pointer stored in `a` at the appropriate index to `x`
                mstore(add(shl(0x05, i), a), x)

                // Set the transient storage mapping for `token` to point at `x`
                tstore(token, x)

                // Initialize `x`
                mstore(x, token)
                mstore(add(0x20, x), shl(0xf8, i))

                // `delta` remains zero
            }
            default {
                delta := signextend(0x1f, mload(add(0x20, x)))
            }
        }
    }

    function swap(TokenNote[] memory a, TokenNote memory x, TokenNote memory y) internal pure {
        assembly ("memory-safe") {
            let x_i_ptr := add(0x20, x)
            let x_note := mload(x_i_ptr)
            let x_i := shr(0xf8, x_note)

            let y_i_ptr := add(0x20, y)
            let y_note := mload(y_i_ptr)
            let y_i := shr(0xf8, y_note)

            // Swap the indices in `x` and `y`
            let mask := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
            mstore(x_i_ptr, or(and(mask, x_note), shl(0xf8, y_i)))
            mstore(y_i_ptr, or(and(mask, y_note), shl(0xf8, x_i)))

            // Swap the indirection pointers in `a` (`x_i` and `y_i` are 1-indexed)
            mstore(add(shl(0x05, x_i), a), y)
            mstore(add(shl(0x05, y_i), a), x)
        }
    }

    function pop(TokenNote[] memory a) internal pure {
        assembly ("memory-safe") {
            let len := mload(a)
            let end := add(shl(0x05, len), a)

            // Clear the backpointer (index) in the referred-to `TokenNote`
            let i_ptr := add(0x20, mload(end))
            mstore(i_ptr, and(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, mload(i_ptr)))
            // We do not deallocate the `TokenNote`

            mstore(a, sub(len, 0x01))
        }
    }

    /// This only deallocates the transient storage mapping. The objects in memory remain as-is and
    /// may still be used. This does not deallocate any memory.
    function destruct(TokenNote[] memory a) internal {
        assembly ("memory-safe") {
            for {
                let i := add(add(0x20, shl(0x05, _MAX_TOKENS)), a)
                let end
                {
                    let len := mload(i)
                    i := add(0x20, i)
                    end := add(shl(0x06, len), i)
                }
            } lt(i, end) {
                i := add(0x40, i)
            } {
                tstore(mload(i), 0x00)
            }
        }
    }
}

abstract contract UniswapV4 is SettlerAbstract, FreeMemory {
    using UnsafeMath for uint256;
    using UnsafeMath for int256;
    using CreditDebt for int256;
    using SafeTransferLib for IERC20;
    using UnsafeArray for TokenDelta[];
    using UnsafePoolManager for IPoolManager;
    using NotedTokens for NotedTokens.TokenNote[];

    //// These two functions are the entrypoints to this set of actions. Because UniV4 has mandatory
    //// callbacks, and the vast majority of the business logic has to be executed inside the
    //// callback, they're pretty minimal. Both end up inside the last function in this file
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

    function sellToUniswapV4(
        address recipient,
        IERC20 sellToken,
        uint256 bps,
        bool feeOnTransfer,
        bytes memory fills,
        uint256 amountOutMin
    ) internal returns (uint256) {
        if (amountOutMin > uint128(type(int128).max)) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }
        if (bps > BASIS) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }
        bytes memory data;
        assembly ("memory-safe") {
            data := mload(0x40)

            let pathLen := mload(fills)
            mcopy(add(0xb3, data), add(0x20, fills), pathLen)

            mstore(add(0x93, data), bps)
            mstore(add(0x91, data), sellToken)
            mstore(add(0x7d, data), address()) // payer
            mstore(add(0x68, data), amountOutMin)
            mstore(add(0x58, data), recipient)
            mstore(add(0x44, data), add(0x4f, pathLen))
            mstore(add(0x24, data), 0x20)
            mstore(add(0x04, data), 0x48c89491) // selector for `unlock(bytes)`
            mstore(data, add(0x93, pathLen))
            mstore8(add(0x88, data), feeOnTransfer)

            mstore(0x40, add(add(0xb3, data), pathLen))
        }
        return uint256(
            bytes32(
                abi.decode(
                    _setOperatorAndCall(
                        address(POOL_MANAGER), data, uint32(IUnlockCallback.unlockCallback.selector), _uniV4Callback
                    ),
                    (bytes)
                )
            )
        );
    }

    function sellToUniswapV4VIP(
        address recipient,
        bool feeOnTransfer,
        bytes memory fills,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes memory sig,
        uint256 amountOutMin
    ) internal returns (uint256) {
        if (amountOutMin > uint128(type(int128).max)) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }
        bool isForwarded = _isForwarded();
        bytes memory data;
        assembly ("memory-safe") {
            data := mload(0x40)

            let pathLen := mload(fills)
            let sigLen := mload(sig)

            let ptr := add(0x112, data)
            mcopy(ptr, add(0x20, fills), pathLen)
            ptr := add(ptr, pathLen)
            // TODO: encode sig length in 3 bytes instead of 32
            mcopy(ptr, add(0x20, sig), sigLen)
            ptr := add(ptr, sigLen)
            mstore(ptr, sigLen)
            ptr := add(0x20, ptr)

            mstore(0x40, ptr)

            mstore8(add(0x111, data), isForwarded)
            mcopy(add(0xd1, data), add(0x20, permit), 0x40)
            mcopy(add(0x91, data), mload(permit), 0x40)

            mstore(add(0x7d, data), 0x00) // payer
            mstore(add(0x68, data), amountOutMin)
            mstore(add(0x58, data), recipient)
            mstore(add(0x44, data), add(0x132, add(pathLen, sigLen)))
            mstore(add(0x24, data), 0x20)
            mstore(add(0x04, data), 0x48c89491) // selector for `unlock(bytes)`
            mstore(data, add(0x176, add(pathLen, sigLen)))
            mstore8(add(0x89, data), feeOnTransfer)
        }
        return uint256(
            bytes32(
                abi.decode(
                    _setOperatorAndCall(
                        address(POOL_MANAGER), data, uint32(IUnlockCallback.unlockCallback.selector), _uniV4Callback
                    ),
                    (bytes)
                )
            )
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
    //// The two major pieces of state that are maintained through the callback are `IERC20[] memory
    //// notes` and `State memory state`
    ////
    //// `notes` keeps track of the full list of all tokens that have been touched throughout the
    //// callback. The first token in the list is the sell token (any debt will be paid to the pool
    //// manager). The last token in the list is the buy token (any credit will be checked against
    //// the slippage limit). All other tokens in the list are some combination of intermediate
    //// tokens or multiplex-out tokens (any credit will be swept back into Settler). To avoid doing
    //// a linear scan each time a new token is encountered, the transient storage slot named by
    //// that token stores the index (actually index * 32 + 32) of the token in the array. The
    //// function `_take` is responsible for iterating over the list of tokens and withdrawing any
    //// credit to the appropriate recipient.
    ////
    //// `state` exists to reduce stack pressure and to simplify and gas-optimize the process of
    //// swapping. By keeping track of the sell token on each hop, we're able to compress the
    //// representation of the fills required to satisfy the swap. Most often in a swap, the tokens
    //// in adjacent fills are somewhat in common. By caching these tokens, we avoid having them
    //// appear multiple times in the calldata. Additionally, this caching helps us avoid reading
    //// the credit of each fill's sell token.

    /// Because we have to ABIEncode the arguments to `.swap(...)` and copy the `hookData` from
    /// calldata into memory, we save gas be deallocating at the end of this function.
    function _swap(PoolKey memory key, IPoolManager.SwapParams memory params, bytes calldata hookData)
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
    uint256 private constant _HOP_LENGTH = 32;

    /// To save stack and to simplify the following helper functions, we cache a bunch of state
    /// about the swap. Note that `globalSellAmount` is practically unused when selling a FoT token.
    struct State {
        IERC20 globalSellToken;
        uint256 globalSellAmount;
        IERC20 sellToken;
        uint256 sellAmount;
        IERC20 buyToken;
        uint256 buyAmount;
    }

    /// Decode a `PoolKey` from its packed representation in `bytes`. Returns the suffix of the
    /// bytes that are not consumed in the decoding process. The first byte of `data` describes
    /// which of the compact representations for the hop is used.
    ///   0 -> sell and buy tokens remain unchanged from the previous fill (pure multiplex)
    ///   1 -> sell token remains unchanged from the previous fill, buy token is read from `data` (diamond multiplex)
    ///   2 -> sell token becomes the buy token from the previous fill, new buy token is read from `data` (multihop)
    ///   3 -> both sell and buy token are read from `data`
    ///
    /// This function is also responsible for calling `_note`, which maintains the `notes` array and
    /// the corresponding mapping in transient storage
    function _getPoolKey(
        PoolKey memory key,
        IERC20[] memory notes,
        State memory state,
        bool feeOnTransfer,
        bytes calldata data
    ) private returns (bool, bytes calldata) {
        uint256 caseKey = uint8(bytes1(data));
        data = data[1:];
        if (caseKey != 0) {
            if (caseKey > 1) {
                if (caseKey == 2) {
                    (state.sellToken, state.sellAmount) = (state.buyToken, state.buyAmount);
                } else {
                    assert(caseKey == 3);

                    state.sellToken = IERC20(address(uint160(bytes20(data))));
                    data = data[20:];
                    state.sellAmount = _getCredit(state, feeOnTransfer, state.sellToken);
                }
            }
            state.buyToken = IERC20(address(uint160(bytes20(data))));
            data = data[20:];

            // TODO: it would be a noticeable gas improvement to only note tokens when
            // **un**-setting `buyToken`. That is, when overwriting it, note the old value. This
            // removes some of the awkwardness with `_initializeNotes` and would avoid an extra
            // `tload`/`tstore`. This does mean adding an extra check in `_getTokenDeltas` where we
            // check if the last token in `notes` is the same as `state.buyToken`, and if it is,
            // popping. On the whole, though, it should be an optimization.
            if (_note(notes, state.buyToken)) {
                delete state.buyAmount;
            } else {
                state.buyAmount = _getCredit(state.buyToken);
            }
        }

        bool zeroForOne = state.sellToken < state.buyToken;
        (key.token0, key.token1) = zeroForOne ? (state.sellToken, state.buyToken) : (state.buyToken, state.sellToken);
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

    /// Makes a `staticcall` to `POOL_MANAGER.exttload` to obtain the debt of the given
    /// token. Reverts if the given token instead has credit.
    function _getDebt(IERC20 token) private view returns (uint256) {
        bytes32 key;
        assembly ("memory-safe") {
            mstore(0x00, address())
            mstore(0x20, and(0xffffffffffffffffffffffffffffffffffffffff, token))
            key := keccak256(0x00, 0x40)
        }
        int256 delta = int256(uint256(IPoolManager(_operator()).exttload(key)));
        return delta.asDebt(token);
    }

    /// Makes a `staticcall` to `POOL_MANAGER.exttload` to obtain the credit of the given
    /// token. Reverts if the given token instead has debt.
    function _getCredit(IERC20 token) private view returns (uint256) {
        bytes32 key;
        assembly ("memory-safe") {
            mstore(0x00, address())
            mstore(0x20, and(0xffffffffffffffffffffffffffffffffffffffff, token))
            key := keccak256(0x00, 0x40)
        }
        int256 delta = int256(uint256(IPoolManager(_operator()).exttload(key)));
        return delta.asCredit(token);
    }

    /// A more complex version of `_getCredit`. There is additional logic that must be applied when
    /// `token` might be the global sell token. Handles that case elegantly. Reverts if the given
    /// token has debt.
    function _getCredit(State memory state, bool feeOnTransfer, IERC20 token) private view returns (uint256) {
        if (token == state.globalSellToken) {
            if (feeOnTransfer) {
                return _getCredit(token);
            } else {
                return state.globalSellAmount - _getDebt(token);
            }
        } else {
            return _getCredit(token);
        }
    }

    /// This function assumes that `notes` has been initialized by Solidity with a length of exactly
    /// `_MAX_TOKENS`. We then truncate the array to a length of 1, store `token`, and make an entry
    /// in the transient storage mapping. We do *NOT* deallocate memory. This ensures that the
    /// length of `notes` can later be increased to store more tokens, up to the limit of
    /// `_MAX_TOKENS`. `_note` below will revert upon reaching that limit.
    function _initializeNotes(IERC20[] memory notes, IERC20 token) private {
        assembly ("memory-safe") {
            token := and(0xffffffffffffffffffffffffffffffffffffffff, token)
            mstore(notes, 0x01)
            mstore(add(0x20, notes), token)
            tstore(token, 0x20)
        }
    }

    /// `_note` is responsible for maintaining `notes` and the corresponding mapping. The return
    /// value `isNew` indicates that the token has been noted. That is, the token has been appended
    /// to the `notes` array and a corresponding entry has been made in the transient storage
    /// mapping. If `token` is not new, and it is not the token at the end of `notes`, we swap it to
    /// the end (and make corresponding changes to the transient storage mapping). If `token` is not
    /// new, and it is the token at the end of `notes`, this function is a no-op.  This function
    /// reverts with a Panic with code 0x32 (indicating an out-of-bounds array access) if more than
    /// `_MAX_TOKENS` tokens are involved in the UniV4 fills.
    function _note(IERC20[] memory notes, IERC20 token) private returns (bool isNew) {
        assembly ("memory-safe") {
            token := and(0xffffffffffffffffffffffffffffffffffffffff, token)
            let notesLen := shl(0x05, mload(notes))
            let notesLast := add(notes, notesLen)
            let oldToken := mload(notesLast)
            if iszero(eq(oldToken, token)) {
                // Either `token` is new or it's in the wrong spot in `notes`
                let tokenIndex := tload(token)
                switch tokenIndex
                case 0 {
                    // `token` is new. Push it onto the end of `notes`.
                    isNew := true

                    notesLen := add(0x20, notesLen)
                    if gt(notesLen, shr(0x05, _MAX_TOKENS)) {
                        mstore(0x00, 0x4e487b71) // selector for `Panic(uint256)`
                        mstore(0x20, 0x32) // array out of bounds
                        revert(0x1c, 0x24)
                    }

                    mstore(add(notesLen, notes), token)
                    tstore(token, notesLen)

                    mstore(notes, shr(0x05, notesLen))
                }
                default {
                    // `token` is not new, but it's in the wrong spot. Swap it with the token
                    // that's already there.
                    mstore(notesLast, token)
                    mstore(add(notes, tokenIndex), oldToken)
                    tstore(token, notesLen)
                    tstore(oldToken, tokenIndex)
                }
            }
        }
    }

    struct TokenDelta {
        IERC20 token;
        int256 creditDebt;
    }

    /// Settling out the credits and debt at the end of a series of fills requires reading the
    /// deltas for each token we touched from the transient storage of the pool manager. We do this
    /// in bulk using `exttload(bytes32[])`. Then we parse the response, omitting each token with
    /// zero delta. This is done in assembly for efficiency _and_ so that we can clear the transient
    /// storage mapping. This function is only used by `_take`, which implements the corresponding
    /// business logic.
    function _getTokenDeltas(IERC20[] memory notes) private returns (TokenDelta[] memory deltas) {
        // TODO: the number of tokens with nonzero deltas is stored in slot
        // 0x7d4b3164c6e45b97e7d87b7125a44c5828d005af88f9d751cfd78729c5d99a0b --
        // bytes32(uint256(keccak256("NonzeroDeltaCount")) - 1) it might optimize the simple cases
        // here to either cache this value in memory or to read it first before tloading all of the
        // delta slots from the pool manager
        //
        // I think that the best way to do this is to apply the optimization described in
        // `_getPoolKey`, noting the buy token only when moving on to a new buy token, and then
        // using a swap-and-pop to drop each token from `notes` as we zero its delta. We can also
        // remove the global sell token from the front of `notes`, making a potential implementation
        // more straightforward, because it's already stored in `state.globalSellToken`
        assembly ("memory-safe") {
            // We're going to allocate memory. We must correctly restore the free pointer later
            let ptr := mload(0x40)

            mstore(ptr, 0x9bf6645f) // selector for `exttload(bytes32[])`
            mstore(add(0x20, ptr), 0x20)

            // We need to hash the token with `address(this)` to obtain the transient slot that
            // stores the delta in POOL_MANAGER. This avoids duplicated writes later.
            mstore(0x00, address())

            // `len` is one word short of the actual length of `notes`. the last element of `notes`
            // is the buy token and is handled separately. we already know the credit of that
            // token. it is `state.buyAmount`.
            let len := sub(shl(0x05, mload(notes)), 0x20)
            mstore(add(0x40, ptr), shr(0x05, len))

            for {
                let src := add(0x20, notes)
                let dst := add(0x60, ptr)
                let end := add(src, len)
            } lt(src, end) {
                src := add(0x20, src)
                dst := add(0x20, dst)
            } {
                // load the token from the array
                let token := mload(src)

                // clear the memoization transient slot
                tstore(token, 0x00)

                // compute the slot that POOL_MANAGER uses to store the delta; store it in the
                // incremental calldata
                mstore(0x20, token)
                mstore(dst, keccak256(0x00, 0x40))
            }

            // perform the call to `exttload(bytes32[])`; check for failure
            if iszero(staticcall(gas(), caller(), add(0x1c, ptr), add(0x44, len), ptr, add(0x40, len))) {
                // `exttload(bytes32[])` can only fail by OOG. no need to check the returndata
                revert(0x00, 0x00)
            }

            // there is 1 wasted slot of memory here (it stores 0x20), but we don't correct for it
            deltas := add(0x20, ptr)
            // we know that the returndata is correctly ABIEncoded, so we skip the first 2 slots
            let src := add(0x40, ptr)
            ptr := add(len, src)
            let dst := src
            for { let end := ptr } lt(src, end) { src := add(0x20, src) } {
                // dst is updated below

                let creditDebt := mload(src)
                if creditDebt {
                    mstore(dst, ptr)
                    dst := add(0x20, dst)
                    mcopy(ptr, add(notes, sub(src, deltas)), 0x20)
                    mstore(add(0x20, ptr), creditDebt)
                    ptr := add(0x40, ptr)
                }
            }

            // set length
            mstore(deltas, shr(0x05, sub(sub(dst, deltas), 0x20)))

            // update the free memory pointer
            mstore(0x40, ptr)
        }
    }

    /// `_take` is responsible for removing the accumulated credit in each token from the pool
    /// manager. It returns the settled global `sellAmount` as the amount that must be paid to the
    /// pool manager (there is a subtle interaction here with the `feeOnTransfer` flag) as well as
    /// the settled global `buyAmount`, after checking it against the slippage limit. This function
    /// uses `_getTokenDeltas` to do the dirty work of enumerating the tokens involved in all the
    /// fills and reading their credit/debt from the transient storage of the pool manager. Each
    /// token with credit causes a corresponding call to `POOL_MANAGER.take`. Any token with debt
    /// (except the first) causes a revert. The last token in `notes` has its slippage checked.
    function _take(IERC20[] memory notes, State memory state, address payer, address recipient, uint256 minBuyAmount)
        private
        DANGEROUS_freeMemory
        returns (uint256 sellAmount, uint256 buyAmount)
    {
        TokenDelta[] memory deltas = _getTokenDeltas(notes);
        uint256 length = deltas.length;

        {
            TokenDelta memory sellDelta = deltas[0]; // revert on out-of-bounds is desired
            (IERC20 token, int256 creditDebt) = (sellDelta.token, sellDelta.creditDebt);
            if (token == state.sellToken) {
                if (creditDebt > 0) {
                    // It's only possible to reach this branch when selling a FoT token and
                    // encountering a partial fill. This is a fairly rare occurrence, so it's
                    // poorly-optimized. It also incurs an additional tax.
                    IPoolManager(_operator()).unsafeTake(
                        token, payer == address(this) ? address(this) : _msgSender(), uint256(creditDebt)
                    );
                    // sellAmount remains zero
                } else {
                    // The actual sell amount (inclusive of any partial filling) is the debt of the
                    // first token. This is the most common branch to hit.
                    sellAmount = uint256(creditDebt.unsafeNeg());
                }
            } else if (length != 0) {
                // This branch is encountered when selling a FoT token, not encountering a partial
                // fill (filling exactly), and then having to multiplex *OUT* more than 1
                // token. This is a fairly rare case.
                IPoolManager(_operator()).unsafeTake(token, address(this), creditDebt.asCredit(token));
                // sellAmount remains zero
            }
            // else {
            //     // This branch is encountered when selling a FoT token, not encountering a
            //     // partial fill (filling exactly), and then buying exactly 1 token. This is the
            //     // second most common branch. This is also elegantly handled by simply falling
            //     // through to the last block of this function
            //
            //     // sellAmount remains zero
            // }
        }

        // Sweep any dust or any non-UniV4 multiplex-out into Settler.
        for (uint256 i = 1; i < length; i = i.unsafeInc()) {
            (IERC20 token, int256 creditDebt) = deltas.unsafeGet(i);
            IPoolManager(_operator()).unsafeTake(token, address(this), creditDebt.asCredit(token));
        }

        // TODO: Remove this last branch from this function; it doesn't have much/anything to do
        // with the other cases now that the buy token isn't in `notes`

        // The last token of `notes` is not checked. We read its information from `state`
        // instead. It is the global buy token. Check the slippage limit. Transfer to the recipient.
        {
            IERC20 token = state.buyToken;
            buyAmount = state.buyAmount;
            if (buyAmount < minBuyAmount) {
                if (token == IERC20(address(0))) {
                    token = ETH_ADDRESS;
                }
                revert TooMuchSlippage(token, minBuyAmount, buyAmount);
            }
            IPoolManager(_operator()).unsafeTake(token, recipient, buyAmount);
        }
    }

    function _settleERC20(
        IERC20 sellToken,
        address payer,
        uint256 sellAmount,
        ISignatureTransfer.PermitTransferFrom calldata permit,
        bool isForwarded,
        bytes calldata sig
    ) private {
        IPoolManager(_operator()).unsafeSync(sellToken);
        if (payer == address(this)) {
            sellToken.safeTransfer(_operator(), sellAmount);
        } else {
            ISignatureTransfer.SignatureTransferDetails memory transferDetails =
                ISignatureTransfer.SignatureTransferDetails({to: _operator(), requestedAmount: sellAmount});
            _transferFrom(permit, transferDetails, sig, isForwarded);
        }
        IPoolManager(_operator()).settle();
    }

    function unlockCallback(bytes calldata data) private returns (bytes memory) {
        // These values are user-supplied
        address recipient = address(uint160(bytes20(data)));
        data = data[20:];
        uint256 minBuyAmount = uint128(bytes16(data));
        data = data[16:];
        bool feeOnTransfer = uint8(bytes1(data)) != 0;
        data = data[1:];

        // `payer` is special and is authenticated
        address payer = address(uint160(bytes20(data)));
        data = data[20:];

        State memory state;
        state.globalSellToken = IERC20(address(uint160(bytes20(data))));
        // We don't advance `data` here because there's a special interaction between `payer`,
        // `sellToken`, and `permit` that's handled below.

        // We could do this anytime before we begin swapping.
        IERC20[] memory notes = new IERC20[](_MAX_TOKENS);
        // This is awkward and not gas-optimal, duplicating work with `_note` on the first hop, but
        // it avoids a bug where the representation of selling Ether (zero) collides with the
        // representation of an empty memory array (also zero).
        _initializeNotes(notes, state.globalSellToken);

        ISignatureTransfer.PermitTransferFrom calldata permit;
        bool isForwarded;
        bytes calldata sig;
        // This assembly block is just here to appease the compiler. We only use `permit` and `sig`
        // in the codepaths where they are set away from the values initialized here.
        assembly ("memory-safe") {
            permit := calldatasize()
            sig.offset := calldatasize()
            sig.length := 0x00
        }

        // TODO: it would be really nice to be able to custody-optimize multihops by calling
        // `unlock` at the beginning of the swap and doing the dispatch loop inside the
        // callback. But this introduces additional attack surface and may not even be that much
        // more efficient considering all the `calldatacopy`ing required and memory expansion.
        if (state.globalSellToken == ETH_ADDRESS) {
            assert(payer == address(this));
            data = data[20:];

            uint16 bps = uint16(bytes2(data));
            data = data[2:];
            unchecked {
                state.globalSellAmount = (address(this).balance * bps).unsafeDiv(BASIS);
            }
            state.globalSellToken = IERC20(address(0));
        } else {
            if (payer == address(this)) {
                data = data[20:];

                uint16 bps = uint16(bytes2(data));
                data = data[2:];
                unchecked {
                    state.globalSellAmount = (state.globalSellToken.balanceOf(address(this)) * bps).unsafeDiv(BASIS);
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

                state.globalSellAmount = _permitToSellAmountCalldata(permit);
            }

            if (feeOnTransfer) {
                _settleERC20(state.globalSellToken, payer, state.globalSellAmount, permit, isForwarded, sig);
            }
        }

        // Now that we've unpacked and decoded the header, we can begin decoding the array of swaps
        // and executing them.
        PoolKey memory key;
        IPoolManager.SwapParams memory params;

        while (data.length >= _HOP_LENGTH) {
            uint16 bps = uint16(bytes2(data));
            data = data[2:];

            bool zeroForOne;
            (zeroForOne, data) = _getPoolKey(key, notes, state, feeOnTransfer, data);
            bytes calldata hookData;
            (hookData, data) = _getHookData(data);

            params.zeroForOne = zeroForOne;
            unchecked {
                params.amountSpecified = int256((state.sellAmount * bps).unsafeDiv(BASIS)).unsafeNeg();
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
                state.sellAmount -= settledSellAmount.asDebt(state.sellToken);
                unchecked {
                    // if `state.buyAmount` overflows an `int128`, we'll get a revert inside the
                    // pool manager later
                    state.buyAmount += settledBuyAmount.asCredit(state.buyToken);
                }
            }
        }

        // `data` has been consumed. All that remains is to settle out the net result of all the
        // swaps. If we somehow incurred a debt in any token other than `sellToken`, we're going to
        // revert. Any credit in any token other than `buyToken` will be swept to
        // Settler. `buyToken` will be sent to `recipient`.
        {
            (uint256 sellAmount, uint256 buyAmount) = _take(notes, state, payer, recipient, minBuyAmount);
            if (state.globalSellToken == IERC20(address(0))) {
                IPoolManager(_operator()).settle{value: sellAmount}();
            } else if (sellAmount != 0) {
                // `sellAmount == 0` only happens when selling a FoT token, because we settled that flow
                // *BEFORE* beginning the swap
                _settleERC20(state.globalSellToken, payer, sellAmount, permit, isForwarded, sig);
            }
            return bytes.concat(bytes32(buyAmount));
        }
    }
}

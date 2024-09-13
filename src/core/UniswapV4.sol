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

import {
    PoolKey, BalanceDelta, IHooks, IPoolManager, POOL_MANAGER, IUnlockCallback
} from "./UniswapV4Types.sol";

library UnsafeArray {
    function unsafeGet(UniswapV4.CurrencyDelta[] memory a, uint256 i)
        internal
        pure
        returns (IERC20 currency, int256 creditDebt)
    {
        assembly ("memory-safe") {
            let r := mload(add(a, add(0x20, shl(0x05, i))))
            currency := mload(r)
            creditDebt := mload(add(0x20, r))
        }
    }
}

library CreditDebt {
    using UnsafeMath for int256;

    function asCredit(int256 delta, IERC20 currency) internal pure returns (uint256) {
        if (delta < 0) {
            revert DeltaNotPositive(currency);
        }
        return uint256(delta);
    }

    function asDebt(int256 delta, IERC20 currency) internal pure returns (uint256) {
        if (delta > 0) {
            revert DeltaNotNegative(currency);
        }
        return uint256(delta.unsafeNeg());
    }
}

abstract contract UniswapV4 is SettlerAbstract, FreeMemory {
    using UnsafeMath for uint256;
    using UnsafeMath for int256;
    using CreditDebt for int256;
    using SafeTransferLib for IERC20;
    using UnsafeArray for CurrencyDelta[];

    //// These two functions are the entrypoints to this set of actions. Because UniV4 has mandatory
    //// callbacks, and the vast majority of the business logic has to be executed inside the
    //// callback, they're pretty minimal. Both end up inside the last function in this file
    //// `unlockCallback`, which is where most of the business logic lives. Primarily, these
    //// functions are concerned with correctly encoding the argument to
    //// `POOL_MANAGER.unlock(...)`. Pay special attention to the `payer` field, which is what
    //// signals to the callback whether we should be spending a coupon.

    function sellToUniswapV4(
        address recipient,
        IERC20 sellToken,
        uint256 bps,
        bool feeOnTransfer,
        bytes memory path,
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

            let pathLen := mload(path)
            mcopy(add(0xb3, data), add(0x20, path), pathLen)

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
        bytes memory path,
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

            let pathLen := mload(path)
            let sigLen := mload(sig)

            let ptr := add(0x112, data)
            mcopy(ptr, add(0x20, path), pathLen)
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
    ///   0 -> buy and sell tokens remain unchanged from the previous fill
    ///   1 -> sell token remains unchanged from the previous fill, buy token is read from `data`
    ///   2 -> sell token becomes the buy token from the previous fill, new buy token is read from `data`
    ///   3 -> both buy and sell token are read from `data`
    ///
    /// This function is also responsible for calling `_note`, which maintains the `notes` array and
    /// the corresponding mapping in transient storage
    function _getPoolKey(
        IERC20[] memory notes,
        PoolKey memory key,
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
            if (_note(notes, state.buyToken)) {
                delete state.buyAmount;
            } else {
                // TODO: add a flag to allow skipping `_getCredit` in cases where it doesn't matter
                state.buyAmount = _getCredit(state.buyToken);
            }
        }

        bool zeroForOne = state.sellToken < state.buyToken;
        (key.currency0, key.currency1) = zeroForOne ? (state.sellToken, state.buyToken) : (state.buyToken, state.sellToken);
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
    function _getDebt(IERC20 currency) private view returns (uint256) {
        bytes32 key;
        assembly ("memory-safe") {
            mstore(0x00, address())
            mstore(0x20, and(0xffffffffffffffffffffffffffffffffffffffff, currency))
            key := keccak256(0x00, 0x40)
        }
        int256 delta = int256(uint256(IPoolManager(_operator()).exttload(key)));
        return delta.asDebt(currency);
    }

    /// Makes a `staticcall` to `POOL_MANAGER.exttload` to obtain the credit of the given
    /// token. Reverts if the given token instead has debt.
    function _getCredit(IERC20 currency) private view returns (uint256) {
        bytes32 key;
        assembly ("memory-safe") {
            mstore(0x00, address())
            mstore(0x20, and(0xffffffffffffffffffffffffffffffffffffffff, currency))
            key := keccak256(0x00, 0x40)
        }
        int256 delta = int256(uint256(IPoolManager(_operator()).exttload(key)));
        return delta.asCredit(currency);
    }

    /// A more complex version of `_getCredit`. There is additional logic that must be applied when
    /// `currency` might be the global sell token. Handles that case elegantly. Reverts if the given
    /// token has debt.
    function _getCredit(State memory state, bool feeOnTransfer, IERC20 currency) private view returns (uint256) {
        if (currency == state.globalSellToken) {
            if (feeOnTransfer) {
                return _getCredit(currency);
            } else {
                return state.globalSellAmount - _getDebt(currency);
            }
        } else {
            return _getCredit(currency);
        }
    }

    /// This is the maximum number of tokens that may be involved in a UniV4 action. If more tokens
    /// than this are involved, then we will Panic with code 0x32 (indicating an out-of-bounds array
    /// access).
    uint256 private constant _MAX_TOKENS = 8;

    /// This function assumes that `notes` has been initialized by Solidity with a length of exactly
    /// `_MAX_TOKENS`. We when truncate the array to a length of 1, store `currency`, and make an
    /// entry in the transient storage mapping. We do *NOT* deallocate memory. This ensures that the
    /// length of `notes` can later be increased to store more tokens, up to the limit of
    /// `_MAX_TOKENS`. `_note` below will revert upon reaching that limit.
    function _initializeNotes(IERC20[] memory notes, IERC20 currency) private {
        assembly ("memory-safe") {
            currency := and(0xffffffffffffffffffffffffffffffffffffffff, currency)
            mstore(notes, 0x01)
            mstore(add(0x20, notes), currency)
            tstore(currency, 0x20)
        }
    }

    /// `_note` is responsible for maintaining `notes` and the corresponding mapping. The return
    /// value `isNew` indicates that the token has been noted. That is, the token has been appended
    /// to the `notes` array and a corresponding entry has been made in the transient storage
    /// mapping. If `currency` is not new, and it is not the token at the end of `notes`, we swap it
    /// to the end (and make corresponding changes to the transient storage mapping). If `currency`
    /// is not new, and it is the token at the end of `notes`, this function is a no-op.  This
    /// function reverts with a Panic with code 0x32 (indicating an out-of-bounds array access) if
    /// more than `_MAX_TOKENS` tokens are involved in the UniV4 fills.
    function _note(IERC20[] memory notes, IERC20 currency) private returns (bool isNew) {
        assembly ("memory-safe") {
            currency := and(0xffffffffffffffffffffffffffffffffffffffff, currency)
            let notesLen := shl(0x05, mload(notes))
            let notesEnd := add(notes, notesLen)
            let oldCurrency := mload(notesEnd)
            if iszero(eq(oldCurrency, currency)) {
                // Either `currency` is new or it's in the wrong spot in `notes`
                let currencyIndex := tload(currency)
                switch currencyIndex
                case 0 {
                    // `currency` is new. Push it onto the end of `notes`.
                    isNew := true

                    notesLen := add(0x20, notesLen)
                    if gt(notesLen, shr(0x05, _MAX_TOKENS)) {
                        mstore(0x00, 0x4e487b71) // selector for `Panic(uint256)`
                        mstore(0x20, 0x32) // array out of bounds
                        revert(0x1c, 0x24)
                    }

                    mstore(add(notesLen, notes), currency)
                    tstore(currency, notesLen)

                    mstore(notes, shr(0x05, notesLen))
                }
                default {
                    // `currency` is not new, but it's in the wrong spot. Swap it with the currency
                    // that's already there.
                    mstore(notesEnd, currency)
                    mstore(add(notes, currencyIndex), oldCurrency)
                    tstore(currency, notesLen)
                    tstore(oldCurrency, currencyIndex)
                }
            }
        }
    }

    struct CurrencyDelta {
        IERC20 currency;
        int256 creditDebt;
    }

    /// Settling out the credits and debt at the end of a series of fills requires reading the
    /// deltas for each token we touched from the transient storage of the pool manager. We do this
    /// in bulk using `exttload(bytes32[])`. Then we parse the response, omitting each currency with
    /// zero delta. This is done in assembly for efficiency _and_ so that we can clear the transient
    /// storage mapping. This function is only used by `_take`, which implements the corresponding
    /// business logic.
    function _getCurrencyDeltas(IERC20[] memory notes) private returns (CurrencyDelta[] memory deltas) {
        assembly ("memory-safe") {
            // We're going to allocate memory. We must correctly restore the free pointer later
            let ptr := mload(0x40)

            mstore(ptr, 0x9bf6645f) // selector for `exttload(bytes32[])`
            mstore(add(0x20, ptr), 0x20)

            // We need to hash the currency with `address(this)` to obtain the transient slot that
            // stores the delta in POOL_MANAGER. This avoids duplicated writes later.
            mstore(0x00, address())

            let len
            for {
                let src := add(0x20, notes)
                let dst := add(0x60, ptr)
                let end := add(src, shl(0x05, _MAX_TOKENS))
            } 0x01 {
                src := add(0x20, src)
                dst := add(0x20, dst)
            } {
                // load the currency from the array
                let currency := mload(src)

                // loop termination condition
                if or(iszero(currency), eq(src, end)) {
                    len := sub(src, notes)
                    mstore(add(0x40, ptr), shr(0x05, len))
                    break
                }

                // clear the memoization transient slot
                tstore(currency, 0x00)

                // compute the slot that POOL_MANAGER uses to store the delta; store it in the
                // incremental calldata
                mstore(0x20, currency)
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

    /// `_take` is responsible for removing the accumulated credit in each currency from the pool
    /// manager. It returns the settled global `sellAmount` as the amount that must be paid to the
    /// pool manager (there is a subtle interaction here with the `feeOnTransfer` flag) as well as
    /// the settled global `buyAmount`, after checking it against the slippage limit. This function
    /// uses `_getCurrencyDeltas` to do the dirty work of enumerating the tokens involved in all the
    /// fills and reading their credit/debt from the transient storage of the pool manager. Each
    /// token with credit causes a corresponding call to `POOL_MANAGER.take`. Any token with debt
    /// (except the first) causes a revert. The last token in `notes` has its slippage checked.
    function _take(IERC20[] memory notes, IERC20 sellToken, address payer, address recipient, uint256 minBuyAmount)
        private
        DANGEROUS_freeMemory
        returns (uint256 sellAmount, uint256 buyAmount)
    {
        CurrencyDelta[] memory deltas = _getCurrencyDeltas(notes);
        uint256 length = deltas.length.unsafeDec();

        {
            CurrencyDelta memory sellDelta = deltas[0]; // revert on out-of-bounds is desired TODO: probably unnecessary
            (IERC20 currency, int256 creditDebt) = (sellDelta.currency, sellDelta.creditDebt);
            if (currency == sellToken) {
                if (creditDebt > 0) {
                    // It's only possible to reach this branch when selling a FoT token and
                    // encountering a partial fill. This is a fairly rare occurrence, so it's
                    // poorly-optimized. It also incurs an additional sell tax.
                    IPoolManager(_operator()).take(
                        currency, payer == address(this) ? address(this) : _msgSender(), uint256(creditDebt)
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
                IPoolManager(_operator()).take(currency, address(this), creditDebt.asCredit(currency));
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
            (IERC20 currency, int256 creditDebt) = deltas.unsafeGet(i);
            IPoolManager(_operator()).take(currency, address(this), creditDebt.asCredit(currency));
        }

        // The last token is the buy token. Check the slippage limit. Transfer to the recipient.
        {
            (IERC20 currency, int256 creditDebt) = deltas.unsafeGet(length);
            buyAmount = creditDebt.asCredit(currency);
            if (buyAmount < minBuyAmount) {
                IERC20 buyToken = currency;
                if (buyToken == IERC20(address(0))) {
                    buyToken = ETH_ADDRESS;
                }
                revert TooMuchSlippage(buyToken, minBuyAmount, buyAmount);
            }
            IPoolManager(_operator()).take(currency, recipient, buyAmount);
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
            IPoolManager(_operator()).sync(state.globalSellToken);

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
            (zeroForOne, data) = _getPoolKey(notes, key, state, feeOnTransfer, data);
            bytes calldata hookData;
            (hookData, data) = _getHookData(data);

            uint256 hopSellAmount;
            unchecked {
                hopSellAmount = (state.sellAmount * bps).unsafeDiv(BASIS);

                // TODO: some hooks may credit some sell amount back. this won't result in reverts
                // due to how `_take` elegantly handles partial fill and ensures that everything is
                // zeroed-out at the end, but it will result in unexpected dust. perhaps there is a
                // clever solution? or alternatively, maybe we need to abandon the `caseKey` logic
                // in `_getPoolKey` and simply read the credit on every fill
                state.sellAmount -= hopSellAmount;
            }

            params.zeroForOne = zeroForOne;
            params.amountSpecified = int256(hopSellAmount).unsafeNeg();
            // TODO: price limits
            params.sqrtPriceLimitX96 = zeroForOne ? 4295128740 : 1461446703485210103287273052203988822378723970341;

            BalanceDelta delta = _swap(key, params, hookData);
            unchecked {
                state.buyAmount +=
                    int256(zeroForOne ? delta.amount1() : delta.amount0()).asCredit(state.buyToken);
            }
        }

        // `data` has been consumed. All that remains is to settle out the net result of all the
        // swaps. If we somehow incurred a debt in any token other than `sellToken`, we're going to
        // revert. Any credit in any token other than `buyToken` will be swept to
        // Settler. `buyToken` will be sent to `recipient`.
        {
            (uint256 sellAmount, uint256 buyAmount) =
                _take(notes, state.globalSellToken, payer, recipient, minBuyAmount);
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

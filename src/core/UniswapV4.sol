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
    Currency, PoolKey, BalanceDelta, IHooks, IPoolManager, POOL_MANAGER, IUnlockCallback
} from "./UniswapV4Types.sol";

library UnsafeArray {
    function unsafeGet(UniswapV4.CurrencyDelta[] memory a, uint256 i)
        internal
        pure
        returns (Currency currency, int256 creditDebt)
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

    function asCredit(int256 delta, Currency currency) internal pure returns (uint256) {
        if (delta < 0) {
            revert DeltaNotPositive(Currency.unwrap(currency));
        }
        return uint256(delta);
    }

    function asDebt(int256 delta, Currency currency) internal pure returns (uint256) {
        if (delta > 0) {
            revert DeltaNotNegative(Currency.unwrap(currency));
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

    function sellToUniswapV4(
        address recipient,
        IERC20 sellToken,
        uint256 bps,
        bool feeOnTransfer,
        bytes memory path,
        uint256 amountOutMin
    ) internal returns (uint256) {
        if (amountOutMin > type(uint128).max) {
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
        if (amountOutMin > type(uint128).max) {
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

    function _swap(PoolKey memory key, IPoolManager.SwapParams memory params, bytes calldata hookData)
        private
        DANGEROUS_freeMemory
        returns (BalanceDelta)
    {
        return IPoolManager(_operator()).swap(key, params, hookData);
    }

    uint256 private constant _HOP_LENGTH = 0;

    struct State {
        bool feeOnTransfer; // TODO: remove this member to the stack
        IERC20 globalSellToken;
        uint256 globalSellAmount;
        IERC20 sellToken;
        uint256 sellAmount;
        IERC20 buyToken;
        uint256 buyAmount;
    }

    /// Decode a `PoolKey` from its packed representation in `bytes`. Returns the suffix of the
    /// bytes that are not consumed in the decoding process
    function _getPoolKey(Currency[] memory notes, PoolKey memory key, State memory state, bytes calldata data)
        private
        pure
        returns (bool, bytes calldata)
    {
        uint256 caseKey = uint8(bytes1(data));
        data = data[1:];
        // 0 -> buy and sell tokens remain the same
        // 1 -> sell token remains the same
        // 2 -> buy token becomes sell token
        // 3 -> completely fresh tokens
        if (caseKey != 0) {
            if (caseKey > 1) {
                if (caseKey == 2) {
                    (state.sellToken, state.sellAmount) = (state.buyToken, state.buyAmount);
                } else {
                    assert(caseKey == 3);

                    state.sellToken = IERC20(address(uint160(bytes20(data))));
                    data = data[20:];
                    state.sellAmount = _getCredit(state, Currency.wrap(address(state.sellToken)));
                }
            }
            state.buyToken = IERC20(address(uint160(bytes20(data))));
            data = data[20:];
            if (caseKey & 4 != 0) {
                state.buyAmount = _getCredit(Currency.wrap(address(state.buyToken)));
            } else {
                delete state.buyAmount;
            }

            _noteToken(notes, Currency.wrap(address(state.buyToken)));
        }

        bool zeroForOne = state.sellToken < state.buyToken;
        if (zeroForOne) {
            key.currency0 = Currency.wrap(address(state.sellToken));
            key.currency1 = Currency.wrap(address(state.buyToken));
        } else {
            key.currency1 = Currency.wrap(address(state.sellToken));
            key.currency0 = Currency.wrap(address(state.buyToken));
        }
        key.fee = uint24(bytes3(data));
        data = data[3:];
        key.tickSpacing = int24(uint24(bytes3(data)));
        data = data[3:];
        key.hooks = IHooks.wrap(address(uint160(bytes20(data))));
        data = data[20:];

        return (zeroForOne, data);
    }

    /// Decode an ABIEncoded `bytes`. Also returns the remainder that wasn't consumed by the
    /// ABIDecoding. Does not follow the "strict" ABIEncoding rules that require padding to a
    /// multiple of 32 bytes.
    function _getHookData(bytes calldata data) private pure returns (bytes calldata hookData, bytes calldata retData) {
        assembly ("memory-safe") {
            hookData.length := shr(0xe8, calldataload(data.offset))
            hookData.offset := add(0x03, data.offset)
            let hop := add(0x03, hookData.length)
            data.offset := add(data.offset, hop)
            data.length := sub(data.length, hop)
        }
    }

    function _getDebt(Currency currency) private view returns (uint256) {
        bytes32 key;
        assembly ("memory-safe") {
            mstore(0x00, address())
            mstore(0x20, and(0xffffffffffffffffffffffffffffffffffffffff, currency))
            key := keccak256(0x00, 0x40)
        }
        int256 delta = int256(uint256(IPoolManager(_operator()).exttload(key)));
        return delta.asDebt(currency);
    }

    function _getCredit(Currency currency) private view returns (uint256) {
        bytes32 key;
        assembly ("memory-safe") {
            mstore(0x00, address())
            mstore(0x20, and(0xffffffffffffffffffffffffffffffffffffffff, currency))
            key := keccak256(0x00, 0x40)
        }
        int256 delta = int256(uint256(IPoolManager(_operator()).exttload(key)));
        return delta.asCredit(currency);
    }

    function _getCredit(State memory state, Currency currency) private view returns (uint256) {
        if (IERC20(Currency.unwrap(currency)) == state.globalSellToken) {
            if (state.feeOnTransfer) {
                return _getCredit(currency);
            } else {
                return state.globalSellAmount - _getDebt(currency);
            }
        } else {
            return _getCredit(currency);
        }
    }

    // TODO: `notes` could be made dynamic with only a little bit of effort, but it would require
    // altering the action encoding so that we can pass that as a parameter
    uint256 private constant _MAX_TOKENS = 8;

    function _initializeNotes(Currency[] memory notes, Currency currency) private {
        assembly ("memory-safe") {
            currency := and(0xffffffffffffffffffffffffffffffffffffffff, currency)
            mstore(notes, 0x01)
            mstore(add(0x20, notes), currency)
            tstore(currency, 0x20)
        }
    }

    function _noteToken(Currency[] memory notes, Currency currency) private {
        assembly ("memory-safe") {
            currency := and(0xffffffffffffffffffffffffffffffffffffffff, currency)
            let currencyIndex := tload(currency)
            let notesLen := shl(0x05, mload(notes))
            if iszero(eq(currencyIndex, notesLen)) {
                switch currencyIndex
                case 0 {
                    notesLen := add(0x20, notesLen)
                    mstore(add(notesLen, notes), currency)
                    tstore(currency, notesLen)

                    notesLen := shr(0x05, notesLen)
                    mstore(notes, notesLen)
                    if gt(notesLen, _MAX_TOKENS) {
                        mstore(0x00, 0x4e487b71) // selector for `Panic(uint256)`
                        mstore(0x20, 0x32) // array out of bounds
                        revert(0x1c, 0x24)
                    }
                }
                default {
                    let notesEnd := add(notes, notesLen)
                    let oldCurrency := mload(notesEnd)

                    mstore(notesEnd, currency)
                    mstore(add(notes, currencyIndex), oldCurrency)
                    tstore(currency, notesLen)
                    tstore(oldCurrency, currencyIndex)
                }
            }
        }
    }

    struct CurrencyDelta {
        Currency currency;
        int256 creditDebt;
    }

    function _getCurrencyDeltas(Currency[] memory notes) private returns (CurrencyDelta[] memory deltas) {
        assembly ("memory-safe") {
            // we're going to both allocate memory. we must correctly restore the free pointer later
            let ptr := mload(0x40)

            mstore(ptr, 0x9bf6645f) // selector for `exttload(bytes32[])`
            mstore(add(0x20, ptr), 0x20)

            // we need to hash the currency with `address(this)` to obtain the transient slot that
            // stores the delta in POOL_MANAGER. this avoids duplication later
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

            // update/restore the free memory pointer
            mstore(0x40, ptr)
        }
    }

    function _take(Currency[] memory notes, IERC20 sellToken, address payer, address recipient, uint256 minBuyAmount)
        private
        DANGEROUS_freeMemory
        returns (uint256 sellAmount, uint256 buyAmount)
    {
        CurrencyDelta[] memory deltas = _getCurrencyDeltas(notes);
        uint256 length = deltas.length.unsafeDec();

        {
            CurrencyDelta memory sellDelta = deltas[0]; // revert on out-of-bounds is desired
            (Currency currency, int256 creditDebt) = (sellDelta.currency, sellDelta.creditDebt);
            if (IERC20(Currency.unwrap(currency)) == sellToken) {
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
            (Currency currency, int256 creditDebt) = deltas.unsafeGet(i);
            IPoolManager(_operator()).take(currency, address(this), creditDebt.asCredit(currency));
        }

        // The last token is the buy token. Check the slippage limit. Transfer to the recipient.
        {
            (Currency currency, int256 creditDebt) = deltas.unsafeGet(length);
            buyAmount = creditDebt.asCredit(currency);
            if (buyAmount < minBuyAmount) {
                IERC20 buyToken = IERC20(Currency.unwrap(currency));
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

        State memory state;
        state.feeOnTransfer = uint8(bytes1(data)) != 0;
        data = data[1:];

        // `payer` is special and is authenticated
        address payer = address(uint160(bytes20(data)));
        data = data[20:];
        state.globalSellToken = IERC20(address(uint160(bytes20(data))));
        // We don't advance `data` here because there's a special interaction between `payer`,
        // `sellToken`, and `permit` that's handled below.

        // We could do this anytime before we begin swapping.
        Currency[] memory notes = new Currency[](_MAX_TOKENS);
        _initializeNotes(notes, Currency.wrap(address(state.globalSellToken)));

        ISignatureTransfer.PermitTransferFrom calldata permit;
        bool isForwarded;
        bytes calldata sig;

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
            IPoolManager(_operator()).sync(Currency.wrap(address(state.globalSellToken)));

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
                    sig.length := calldataload(sig.offset)
                    sig.offset := sub(sig.offset, sig.length)

                    // Remove `permit` and `isForwarded` from the front of `data`
                    data.offset := add(0x75, data.offset)
                    // Remove `sig` from the back of `data`
                    data.length := sub(sub(data.length, 0x95), sig.length)
                }

                state.globalSellAmount = _permitToSellAmountCalldata(permit);
            }

            if (state.feeOnTransfer) {
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
            (zeroForOne, data) = _getPoolKey(notes, key, state, data);
            bytes calldata hookData;
            (hookData, data) = _getHookData(data);

            uint256 hopSellAmount = state.sellAmount;
            unchecked {
                hopSellAmount = (hopSellAmount * bps).unsafeDiv(BASIS);
            }

            params.zeroForOne = zeroForOne;
            params.amountSpecified = int256(hopSellAmount).unsafeNeg();
            // TODO: price limits
            params.sqrtPriceLimitX96 = zeroForOne ? 4295128740 : 1461446703485210103287273052203988822378723970341;

            BalanceDelta delta = _swap(key, params, hookData);
            state.buyAmount +=
                int256(zeroForOne ? delta.amount1() : delta.amount0()).asCredit(Currency.wrap(address(state.buyToken)));
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

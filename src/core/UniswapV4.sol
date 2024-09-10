// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {SettlerAbstract} from "../SettlerAbstract.sol";

import {Panic} from "../utils/Panic.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";

import {TooMuchSlippage, DeltaNotPositive, DeltaNotNegative} from "./SettlerErrors.sol";

import {
    Currency, PoolId, BalanceDelta, IHooks, IPoolManager, POOL_MANAGER, IUnlockCallback
} from "./UniswapV4Types.sol";

abstract contract UniswapV4 is SettlerAbstract {
    using UnsafeMath for uint256;
    using UnsafeMath for int256;
    using SafeTransferLib for IERC20;

    function sellToUniswapV4(address recipient, IERC20 sellToken, uint256 bps, bytes memory path, uint256 amountOutMin)
        internal
        returns (uint256)
    {
        // TODO: encode FoT flag
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
            mcopy(add(0xb2, data), add(0x20, path), pathLen)

            mstore(add(0x92, data), bps)
            mstore(add(0x90, data), sellToken)
            mstore(add(0x7c, data), address()) // payer
            mstore(add(0x68, data), amountOutMin)
            mstore(add(0x58, data), recipient)
            mstore(add(0x44, data), add(0x4e, pathLen))
            mstore(add(0x24, data), 0x20)
            mstore(add(0x04, data), 0x48c89491) // selector for `unlock(bytes)`
            mstore(data, add(0x92, pathLen))

            mstore(0x40, add(add(0xb2, data), pathLen))
        }
        return uint256(
            bytes32(
                abi.decode(
                    _setOperatorAndCall(
                        address(POOL_MANAGER), data, IUnlockCallback.unlockCallback.selector, _uniV4Callback
                    ),
                    (bytes)
                )
            )
        );
    }

    function sellToUniswapV4VIP(
        address recipient,
        bytes memory path,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes memory sig,
        uint256 amountOutMin
    ) internal returns (uint256) {
        // TODO: encode FoT flag
        if (amountOutMin > type(uint128).max) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }
        if (bps > BASIS) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }
        bool isForwarded = _isForwarded();
        bytes memory data;
        assembly ("memory-safe") {
            data := mload(0x40)

            let pathLen := mload(path)
            let sigLen := mload(sig)

            let ptr := add(0x111, data)
            mcopy(ptr, add(0x20, path), pathLen)
            ptr := add(ptr, pathLen)
            mcopy(ptr, add(0x20, sig), sigLen)
            ptr := add(ptr, sigLen)
            mstore(ptr, sigLen)
            ptr := add(0x20, ptr)

            mstore(0x40, ptr)

            mstore8(add(0x110, data), isForwarded)
            mcopy(add(0xd0, data), add(0x20, permit), 0x40)
            mcopy(add(0x90, data), mload(permit), 0x40)

            mstore(add(0x7c, data), 0x00) // payer
            mstore(add(0x68, data), amountOutMin)
            mstore(add(0x58, data), recipient)
            mstore(add(0x44, data), add(0x131, add(pathLen, sigLen)))
            mstore(add(0x24, data), 0x20)
            mstore(add(0x04, data), 0x48c89491) // selector for `unlock(bytes)`
            mstore(data, add(0x175, add(pathLen, sigLen)))
        }
        return uint256(
            bytes32(
                abi.decode(
                    _setOperatorAndCall(
                        address(POOL_MANAGER), data, IUnlockCallback.unlockCallback.selector, _uniV4Callback
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

    function _swap(PoolKey memory key, SwapParams memory params, bytes calldata hookData)
        private
        DANGEROUS_freeMemory
        returns (BalanceDelta)
    {
        return poolManager.swap(poolKey, params, hookData);
    }

    uint256 private constant _HOP_LENGTH = 0;

    /// Decode a `PoolKey` from its packed representation in `bytes`. Returns the suffix of the
    /// bytes that are not consumed in the decoding process
    function _getPoolKey(PoolKey memory key, bytes calldata data) private pure returns (bool, bytes calldata) {}

    /// Decode an ABIEncoded `bytes`. Also returns the remainder that wasn't consumed by the
    /// ABIDecoding. Does not follow the "strict" ABIEncoding rules that require padding to a
    /// multiple of 32 bytes.
    function _getHookData(bytes calldata data) private pure returns (bytes calldata, bytes calldata) {}

    function _getDebt(Currency currency) private view returns (uint256) {
        bytes32 key;
        assembly ("memory-safe") {
            mstore(0x00, address())
            mstore(0x20, and(0xffffffffffffffffffffffffffffffffffffffff, currency))
            key := keccak256(0x00, 0x40)
        }
        int256 delta = int256(uint256(POOL_MANAGER.exttload(key)));
        if (delta > 0) {
            revert DeltaNotNegative(Currency.unwrap(currency));
        }
        return uint256(delta.unsafeNeg());
    }

    function _getCredit(Currency currency) private view returns (uint256) {
        bytes32 key;
        assembly ("memory-safe") {
            mstore(0x00, address())
            mstore(0x20, and(0xffffffffffffffffffffffffffffffffffffffff, currency))
            key := keccak256(0x00, 0x40)
        }
        int256 delta = int256(uint256(POOL_MANAGER.exttload(key)));
        if (delta < 0) {
            revert DeltaNotPositive(Currency.unwrap(currency));
        }
        return uint256(delta);
    }

    uint256 private constant _MAX_TOKENS = 8;

    function _noteToken(Currency[_MAX_TOKENS] memory notes, Currency currency) private returns (uint256) {
        assembly ("memory-safe") {
            currency := and(0xffffffffffffffffffffffffffffffffffffffff, currency)
            mstore(notes, currency)
            tstore(currency, 0x20)
        }
        return 32;
    }

    function _noteToken(Currency[_MAX_TOKENS] memory notes, uint256 notesLen, Currency currency)
        private
        returns (uint256)
    {
        assembly ("memory-safe") {
            currency := and(0xffffffffffffffffffffffffffffffffffffffff, currency)
            let currencyIndex := tload(currency)
            if iszero(eq(currencyIndex, notesLen)) {
                switch currencyIndex
                case 0 {
                    mstore(add(notesLen, notes), currency)
                    notesLen := add(0x20, notesLen)
                    tstore(currency, notesLen)
                    if gt(notesLen, shl(0x05, _MAX_TOKENS)) {
                        mstore(0x00, 0x4e487b71) // selector for `Panic(uint256)`
                        mstore(0x20, 0x32) // array out of bounds
                        revert(0x1c, 0x24)
                    }
                }
                default {
                    let notesEnd := add(notes, sub(notesLen, 0x20))
                    let oldCurrency := mload(notesEnd)

                    mstore(notesEnd, currency)
                    mstore(add(notes, sub(currencyIndex, 0x20)), oldCurrency)
                    tstore(currency, notesLen)
                    tstore(oldCurrency, currencyIndex)
                }
            }
        }
        return notesLen;
    }

    struct Delta {
        Currency currency;
        int256 creditDebt;
    }

    function _getDeltas(Currency[_MAX_TOKENS] memory notes) private returns (Delta[] memory deltas) {
        assembly ("memory-safe") {
            // we're going to both allocate memory and take total control of this slot. we must
            // correctly restore it later
            let ptr := mload(0x40)

            mstore(ptr, 0x9bf6645f) // selector for `exttload(bytes32[])`
            mstore(add(0x20, ptr), 0x20)

            // we need to hash the currency with `address(this)` to obtain the transient slot that
            // stores the delta in POOL_MANAGER. this avoids duplication later
            mstore(0x00, address())

            let len
            for {
                let src := notes
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
            if iszero(staticcall(gas(), POOL_MANAGER, add(0x1c, ptr), add(0x44, len), ptr, add(0x40, len))) {
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
                    mcopy(ptr, add(notes, sub(sub(src, deltas), 0x20)), 0x20)
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

    function _take(
        Currency[_MAX_TOKENS] memory notes,
        IERC20 sellToken,
        address payer,
        address recipient,
        uint256 minBuyAmount
    ) private returns (uint256 sellAmount, uint256 buyAmount) {
        Delta[] memory deltas = _getDeltas(notes);
        uint256 length = deltas.length.unsafeDec();

        {
            Delta memory sellDelta = deltas[0]; // revert on out-of-bounds is desired
            (Currency currency, int256 creditDebt) = (sellDelta.currency, sellDelta.creditDebt);
            if (IERC20(Currency.unwrap(currency)) == sellToken) {
                if (creditDebt > 0) {
                    // It's only possible to reach this branch when selling a FoT token and
                    // encountering a partial fill. This is a fairly rare occurrence, so it's
                    // poorly-optimized. It also incurs an additional sell tax.
                    POOL_MANAGER.take(currency, payer, creditDebt);
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
                if (creditDebt < 0) {
                    revert DeltaNotPositive(Currency.unwrap(currency));
                }
                POOL_MANAGER.take(currency, address(this), uint256(creditDebt));
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
            if (creditDebt < 0) {
                revert DeltaNotPositive(Currency.unwrap(currency));
            }
            POOL_MANAGER.take(currency, address(this), uint256(creditDebt));
        }

        // The last token is the buy token. Check the slippage limit. Transfer to the recipient.
        {
            (Currency currency, int256 creditDebt) = deltas.unsafeGet(length);
            if (creditDebt < 0) {
                revert DeltaNotPositive(Currency.unwrap(currency));
            }
            buyAmount = uint256(creditDebt);
            if (buyAmount < minBuyAmount) {
                IERC20 buyToken = IERC20(Currency.unwrap(currency));
                if (buyToken == IERC20(address(0))) {
                    buyToken = ETH_ADDRESS;
                }
                revert TooMuchSlippage(buyToken, minBuyAmount, buyAmount);
            }
            POOL_MANAGER.take(currency, recipient, buyAmount);
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
        POOL_MANAGER.settle();
    }

    function unlockCallback(bytes calldata data) private returns (bytes memory) {
        // These values are user-supplied
        address recipient = address(uint160(bytes20(data)));
        data = data[20:];
        uint256 minBuyAmount = uint128(bytes16(data));
        data = data[16:];

        // `payer` is special and is authenticated
        address payer = address(uint160(bytes20(data)));
        data = data[20:];
        IERC20 sellToken = IERC20(address(uint160(bytes20(data))));
        // We don't advance `data` here because there's a special interaction between `payer`,
        // `sellToken`, and `permit` that's handled below.

        // We could do this anytime before we begin swapping.
        Currency[_MAX_TOKENS] memory notes;
        uint256 notesLen = _noteToken(notes, Currency.wrap(address(sellToken)));

        uint256 sellAmount;
        ISignatureTransfer.PermitTransferFrom calldata permit;
        bool isForwarded;
        bytes calldata sig;

        // TODO: it would be really nice to be able to custody-optimize multihops by calling
        // `unlock` at the beginning of the swap and doing the dispatch loop inside the
        // callback. But this introduces additional attack surface and may not even be that much
        // more efficient considering all the `calldatacopy`ing required and memory expansion.
        if (sellToken == ETH_ADDRESS) {
            data = data[20:];

            uint16 sellBps = uint16(bytes2(data));
            data = data[2:];
            unchecked {
                sellAmount = (address(this).balance * bps).unsafeDiv(BASIS);
            }
            sellToken = IERC20(address(0));
        } else {
            POOL_MANAGER.sync(Currency.wrap(address(sellToken)));

            if (payer == address(this)) {
                data = data[20:];

                uint16 sellBps = uint16(bytes2(data));
                data = data[2:];
                unchecked {
                    sellAmount = (sellToken.balanceOf(address(this)) * bps).unsafeDiv(BASIS);
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

                sellAmount = _permitToSellAmount(permit);
            }

            if (feeOnTransfer) {
                _settleERC20(sellToken, payer, sellAmount, permit, isForwarded, sig);
            }
        }

        // Now that we've unpacked and decoded the header, we can begin decoding the array of swaps
        // and executing them.
        PoolKey memory key;
        IPoolManager.SwapParams memory params;
        bool zeroForOne;
        while (data.length >= _HOP_LENGTH) {
            uint16 bps = uint16(bytes2(data));
            data = data[2:];

            (zeroForOne, data) = _getPoolKey(key, data);

            Currency hopSellCurrency = zeroForOne ? key.currency0 : key.currency1;
            uint256 hopSellAmount;
            if (IERC20(Currency.unwrap(hopSellCurrency)) == sellToken) {
                // TODO: it might be worth gas-optimizing the case of the first call to `swap` to avoid the overhead of `exttload`
                if (feeOnTransfer) {
                    hopSellAmount = _getCredit(hopSellCurrency);
                } else {
                    hopSellAmount = sellAmount - _getDebt(hopSellCurrency);
                }
            } else {
                hopSellAmount = _getCredit(hopSellCurrency);
            }
            unchecked {
                hopSellAmount = (hopSellAmount * bps).unsafeDiv(BASIS);
            }

            params.zeroForOne = zeroForOne;
            params.amountSpecified = int256(hopSellAmount).unsafeNeg();
            // TODO: price limits
            params.sqrtPriceLimitX96 = zeroForOne ? 4295128740 : 1461446703485210103287273052203988822378723970341;

            notesLen = _noteToken(notes, notesLen, zeroForOne ? key.currency1 : key.currency0);

            bytes calldata hookData;
            (hookData, data) = _getHookData(data);

            _swap(key, params, hookData);
        }

        // `data` has been consumed. All that remains it to settle out the net result of all the
        // swaps. If we somehow incurred a debt in any token other than `sellToken`, we're going to
        // revert. Any credit in any token other than `buyToken` will be swept to
        // Settler. `buyToken` will be sent to `recipient`.
        uint256 buyAmount;
        (sellAmount, buyAmount) = _take(notes, recipient, minBuyAmount);
        if (sellToken == IERC20(address(0))) {
            POOL_MANAGER.settle{value: sellAmount}();
        } else if (sellAmount != 0) {
            // `sellAmount == 0` only happens when selling a FoT token, because we settled that flow
            // *BEFORE* beginning the swap
            _settleERC20(sellToken, payer, sellAmount, permit, isForwarded, sig);
        }

        return bytes(bytes32(buyAmount));
    }
}

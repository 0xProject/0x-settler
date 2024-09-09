// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {SettlerAbstract} from "../SettlerAbstract.sol";

import {Panic} from "../utils/Panic.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";

import {TooMuchSlippage, DeltaNotPositive, DeltaNotPositive} from "./SettlerErrors.sol";

import {Currency, PoolId, BalanceDelta, IHooks, IPoolManager, POOL_MANAGER, IUnlockCallback} from "./UniswapV4Types.sol";

abstract contract UniswapV4 is SettlerAbstract {
    using UnsafeMath for uint256;
    using SafeTransferLib for IERC20;

    function sellToUniswapV4(...) internal returns (uint256) {
        return
            uint256(
                bytes32(
                    abi.decode(
                        _setOperatorAndCall(
                            address(POOL_MANAGER),
                            abi.encodeCall(POOL_MANAGER.unlock, (abi.encode(...))),
                            IUnlockCallback.unlockCallback.selector,
                            _uniV4Callback
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

    function _swap(PoolKey memory key, SwapParams memory params, bytes calldata hookData) private DANGEROUS_freeMemory returns (BalanceDelta) {
        return poolManager.swap(poolKey, params, hookData);
    }

    uint256 private constant _HOP_LENGTH = 0;

    function _getPoolKey(PoolKey memory key, bytes calldata data) private pure returns (bool, bytes calldata) {
    }

    function _getHookData(bytes calldata data) private pure returns (bytes calldata, bytes calldata) {
    }

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

    bytes32 noteIndexMappingSlot = bytes32(0);

    uint256 private constant _MAX_TOKENS = 10;

    function _noteToken(Currency[_MAX_TOKENS] memory notes, uint256 notesLen, Currency currency) private returns (uint256) {
        assembly ("memory-safe") {
            currency := and(0xffffffffffffffffffffffffffffffffffffffff, currency)
            mstore(0x00, currency)
            mstore(0x20, noteIndexMappingSlot)
            let noteIndexSlot := keccak(0x00, 0x40)
            if iszero(tload(noteIndexSlot)) {
                mstore(add(notesLen, notes), currency)
                notesLen := add(0x01, notesLen)
                tstore(noteIndexSlot, notesLen)
                if gt(notesLen, _MAX_TOKENS) {
                    mstore(0x00, 0x4e487b71) // selector for `Panic(uint256)`
                    mstore(0x20, 0x32) // array out of bounds
                    revert(0x1c, 0x24)
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
            let len
            for {
                let src := notes
                let dst := add(0x60, ptr)
                let end := add(src, _MAX_TOKENS)
                mstore(0x00, address())
                mstore(0x40, 0x00)
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

                // clear the mapping slot
                mstore(0x20, currency)
                tstore(keccak(0x20, 0x40), 0x00)

                // compute the slot that POOL_MANAGER uses to store the delta; store it in the
                // incremental calldata
                mstore(dst, keccak(0x00, 0x40))
            }

            // perform the call to `exttload(bytes32[])`; check for failure
            if or(
                  xor(returndatasize(), add(0x40, len)), // TODO: probably unnecessary
                  iszero(staticcall(gas(), POOL_MANAGER, add(0x1c, ptr), add(0x44, len), ptr, add(0x40, len)))
            ) {
                returndatacopy(ptr, 0x00, returndatasize())
                revert(0x00, returndatasize())
            }

            // there is 1 wasted slot of memory here, but we don't correct for it
            deltas := add(0x20, ptr)
            // we know that the returndata is correctly ABIEncoded, so we skip the first 2 slots
            let src := add(0x40, ptr)
            ptr := add(len, src)
            let dst := src
            for {
                let end := add(src, len)
            } lt(src, end) {
                src := add(0x20, src)
                // dst is updated below
            } {
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

    function _take(Currency[_MAX_TOKENS] memory notes, address recipient, uint256 minBuyAmount) private returns (uint256 sellAmount, uint256 buyAmount) {
        Delta[] memory deltas = _getDeltas(notes);

        // The actual sell amount (inclusive of any partial filling) is the debt of the first token
        {
            Delta memory sellDelta = deltas[0]; // revert on out-of-bounds is desired
            if (sellDelta.creditDebt > 0) {
                // debt is negative
                Panic.panic(Panic.ARITHMETIC_OVERFLOW);
            }
            sellAmount = uint256(sellDelta.creditDebt.unsafeNeg());
        }

        // Sweep any dust or any non-UniV4 multiplex into Settler.
        uint256 length = deltas.length - 1; // revert on underflow is desired
        for (uint256 i = 1; i < length; i = i.unsafeInc()) {
            Delta memory delta = deltas.unsafeGet(i);
            (Currency currency, int256 creditDebt) = (delta.currency, delta.creditDebt);
            if (creditDebt < 0) {
                // credit is positive
                Panic.panic(Panic.ARITHMETIC_OVERFLOW);
            }
            POOL_MANAGER.take(currency, address(this), uint256(creditDebt));
        }

        // The last token is the buy token. Check the slippage limit. Sweep to the recipient.
        {
            Delta memory delta = deltas.unsafeGet(length);
            (Currency currency, int256 creditDebt) = (delta.currency, delta.creditDebt);
            if (creditDebt < 0) {
                // credit is positive
                Panic.panic(Panic.ARITHMETIC_OVERFLOW);
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

    function unlockCallback(bytes calldata data) private returns (bytes memory) {
        address payer = address(uint160(bytes20(data)));
        data = data[20:];

        IERC20 sellToken = IERC20(address(uint160(bytes20(data))));
        data = data[20:];

        Currency[_MAX_TOKENS] memory notes;
        uint256 notesLen = _noteToken(notes, 0, Currency.wrap(address(sellToken)));

        uint256 sellAmount;
        ISignatureTransfer.PermitTransferFrom calldata permit;
        bool isForwarded;
        bytes calldata sig;

        // TODO: it would be really nice to be able to custody-optimize multihops by calling
        // `unlock` at the beginning of the swap and doing the dispatch loop inside the
        // callback. But this introduces additional attack surface and may not even be that much
        // more efficient considering all the `calldatacopy`ing required and memory expansion.
        if (sellToken == ETH_ADDRESS) {
            uint16 sellBps = uint16(bytes2(data));
            data = data[2:];
            unchecked {
                sellAmount = (address(this).balance * bps).unsafeDiv(BASIS);
            }
            sellToken = IERC20(address(0));
        } else {
            POOL_MANAGER.sync(Currency.wrap(address(sellToken)));

            if (payer == address(this)) {
                uint16 sellBps = uint16(bytes2(data));
                data = data[2:];
                unchecked {
                    sellAmount = (sellToken.balanceOf(address(this)) * bps).unsafeDiv(BASIS);
                }
            } else {
                assert(payer == address(0));

                assembly ("memory-safe") {
                    // this is super dirty, but it works because although `permit` is aliasing in the
                    // middle of `payer`, because `payer` is all zeroes, it's treated as padding for the
                    // first word of `permit`, which is the sell token
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

                sellAmount = _permitToSellAmount(permit)
            }
        }

        address recipient = address(uint160(bytes20(data)));
        data = data[20:];
        uint256 minBuyAmount = uint128(bytes16(data));
        data = data[16:];

        PoolKey memory key;
        IPoolManager.SwapParams memory params;
        bool zeroForOne;
        while (data.length > _HOP_LENGTH) {
            uint16 bps = uint16(bytes2(data));
            data = data[2:];

            (zeroForOne, data) = _getPoolKey(key, data);

            Currency hopSellCurrency = zeroForOne ? key.currency0 : key.currency1;
            uint256 hopSellAmount;
            if (IERC20(Currency.unwrap(hopSellCurrency)) == sellToken) {
                // TODO: it might be worth gas-optimizing the case of the first call to `swap` to avoid the overhead of `exttload`
                hopSellAmount = sellAmount - _getDebt(hopSellCurrency);
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

        uint256 buyAmount;
        (sellAmount, buyAmount) = _take(notes, recipient, minBuyAmount);
        if (sellToken == IERC20(address(0))) {
            POOL_MANAGER.settle{value: sellAmount}();
        } else {
            if (payer == address(this)) {
                sellToken.safeTransfer(_operator(), sellAmount);
            } else {
                ISignatureTransfer.SignatureTransferDetails memory transferDetails =
                    ISignatureTransfer.SignatureTransferDetails({to: _operator(), requestedAmount: sellAmount});
                _transferFrom(permit, transferDetails, sig, isForwarded);
            }
            POOL_MANAGER.settle();
        }

        return bytes(bytes32(buyAmount));
    }

}

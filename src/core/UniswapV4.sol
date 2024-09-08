// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {SettlerAbstract} from "../SettlerAbstract.sol";

import {Panic} from "../utils/Panic.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";

import {TooMuchSlippage} from "./SettlerErrors.sol";

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
            data.offset := add(0x40, data.offset)
            data.length := calldataload(add(0x20, data.offset))
        }
        return unlockCallback(data);
    }

    function _swap(PoolKey memory key, SwapParams memory params, bytes memory hookData) private DANGEROUS_freeMemory returns (BalanceDelta) {
        return poolManager.swap(poolKey, params, hookData);
    }

    uint256 private constant _HOP_LENGTH = 0;

    function _getPoolKey(PoolKey memory key, bytes calldata data) private pure returns (bool, bytes calldata) {
    }

    function _getHookData(bytes calldata data) private pure returns (bytes calldata, bytes calldata) {
    }

    function _getCredit(Currency currency) internal view returns (uint256) {
        bytes32 key;
        assembly ("memory-safe") {
            mstore(0x00, address())
            mstore(0x20, and(0xffffffffffffffffffffffffffffffffffffffff, currency))
            key := keccak256(0x00, 0x40)
        }
        int256 amount = int256(uint256(POOL_MANAGER.exttload(key)));
        if (amount < 0) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }
        return uint256(amount);
    }

    bytes32 isNotedMappingSlot = bytes32(0);
    bytes32 notedTokensArraySlot = bytes32(1);
    bytes32 arrayOneSlot = 0xb10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf6;
    constructor() {
        assert(arrayOneSlot == keccak256(abi.encode(notedTokensArraySlot)));
    }

    function _noteToken(Currency currency) internal {
        // TODO: this uses transient storage for the array of tokens; it would be more efficient to
        // use memory, but this introduces the question of how much memory to allocate for the
        // array. I've used transient storage here for expediency, but it should be revisited.
        assembly ("memory-safe") {
            currency := and(0xffffffffffffffffffffffffffffffffffffffff, currency)
            mstore(0x00, currency)
            mstore(0x20, isNotedMappingSlot)
            let isNotedSlot := keccak(0x00, 0x40)
            if iszero(tload(isNotedSlot)) {
                tstore(isNotedSlot, true)
                let len := tload(notedTokensArraySlot)
                tstore(notedTokensArraySlot, add(0x01, len))
                tstore(add(arrayOneSlot, len), currency)
            }
        }
    }

    struct Delta {
        Currency currency;
        int256 creditDebt;
    }

    function _getDeltas() private returns (Delta[] memory deltas) {
        assembly ("memory-safe") {
            // we're going to both allocate memory and take total control of this slot. we must
            // correctly restore it later
            let ptr := mload(0x40)

            mstore(ptr, 0x9bf6645f) // selector for `exttload(bytes32[])`
            mstore(add(0x20, ptr), 0x20)
            let len := tload(notedTokensArraySlot)
            tstore(notedTokensArraySlot, 0x00)
            mstore(add(0x40, ptr), len)
            for {
                let src := arrayOneSlot
                let dst := add(0x60, ptr)
                let end := add(src, len)
                mstore(0x00, address())
                mstore(0x40, 0x00)
            } lt(src, end) {
                src := add(0x01, src)
                dst := add(0x20, dst)
            } {
                // load the currency from the array; we defer clearing the slot until after we read
                // the result of `exttload`
                let currency := tload(src)

                // clear the boolean mapping slot
                mstore(0x20, currency)
                tstore(keccak(0x20, 0x40), false)

                // compute the slot that POOL_MANAGER uses to store the delta; store it in the
                // incremental calldata
                mstore(dst, keccak(0x00, 0x40))
            }

            // perform the call to `exttload`; check for failure
            len := shl(0x05, len)
            if or(
                  xor(returndatasize(), add(0x40, len)),
                  // TODO: the code below does incremental returndatacopies and clobbers the result of this `staticcall` with `deltas`
                  // TODO: this also wastes 2 slots of memory compared to the bulk returndatacopy (we know that the first 2 slots are 0x20 and the length, respectively)
                  iszero(staticcall(gas(), POOL_MANAGER, add(0x1c, ptr), add(0x44, len), ptr, add(0x40, len)))
            ) {
                returndatacopy(ptr, 0x00, returndatasize())
                revert(0x00, returndatasize())
            }

            // TODO: this is all wrong; this would've been right if we were using the representation
            // in calldata, but the representation in memory is completely different. fortunately,
            // it does mean that it's now easier for us to `returndatacopy`. Each `Delta` object
            // must be allocated separately from the array. The values in the array just point to
            // `Delta` objects
            let dst := add(0x20, ptr)
            for {
                // we know that the returndata is correctly ABIEncoded, so we skip the first 2 slots
                let src := 0x40
                let end := add(src, len)
            } lt(src, end) {
                src := add(0x20, src)
                // dst is updated below
            } {
                let currencySlot = add(sub(arrayOneSlot, 2), shr(0x05, src))

                // TODO: optimize by doing a bulk returndatacopy
                returndatacopy(0x00, src, 0x20)
                let creditDebt := mload(0x00)

                if creditDebt {
                    mstore(dst, tload(currencySlot))
                    mstore(add(0x20, dst), creditDebt)
                    dst := add(0x40, dst)
                }

                tstore(currencySlot, 0x00)
            }

            // set length
            deltas := ptr
            mstore(deltas, shr(0x06, sub(dst, add(0x20, ptr))))

            // update/restore the free memory pointer
            mstore(0x40, dst)
        }
    }

    function _take(address recipient, uint256 minBuyAmount) private returns (uint256 sellAmount, uint256 buyAmount) {
        Delta[] memory deltas = _getDeltas();

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
        _noteToken(Currency.wrap(address(sellToken)));

        uint256 sellAmount;
        ISignatureTransfer.PermitTransferFrom calldata permit;
        bool isForwarded;
        bytes calldata sig;

        // TODO: it would be really nice to be able to custody-optimize multihops by calling
        // `unlock` at the beginning of the swap and doing the dispatch loop inside the
        // callback. But this introduces additional attack surface and may not even be that much
        // more efficient considering all the `calldatacopy`ing required and memory expansion.
        if (sellToken == ETH_ADDRESS) {
            sellAmount = address(this).balance;
            // TODO: bps
            sellToken = IERC20(address(0));
        } else {
            POOL_MANAGER.sync(Currency.wrap(address(sellToken)));

            if (payer == address(this)) {
                uint256 sellAmount = uint128(bytes16(data));
                data = data[16:];
                // TODO: bps
                sellToken.safeTransfer(_operator(), sellAmount);
            } else {
                assert(payer == address(0));
                // TODO: assert(bps == 0);

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
        uint256 minBuyAmount = uint256(bytes32(data));
        data = data[32:];

        PoolKey memory key;
        IPoolManager.SwapParams memory params;
        bool zeroForOne;
        while (data.length > _HOP_LENGTH) {
            // TODO: bps for multiplex
            // TODO: special-case when the sell token is equal to the global sell token; in that
            // case, we can't use the transient credit to compute the sell amount, we have to do
            // something clever

            (zeroForOne, data) = _getPoolKey(key, data);
            params.zeroForOne = zeroForOne;
            int256 amountSpecified = -int256(sellAmount);
            params.amountSpecified = amountSpecified;
            // TODO: price limits
            params.sqrtPriceLimitX96 = zeroForOne ? 4295128740 : 1461446703485210103287273052203988822378723970341;

            _noteToken(zeroForOne ? key.currency1 : key.currency0);

            bytes calldata hookData;
            (hookData, data) = _getHookData(data);

            BalanceDelta delta = _swap(key, params, hookData);
            sellAmount = uint256(int256((zeroForOne == amountSpecified < 0) ? delta.amount1() : delta.amount0()));
        }

        uint256 buyAmount;
        (sellAmount, buyAmount) = _take(recipient, minBuyAmount);
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

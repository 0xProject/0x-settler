// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {IERC20} from "../IERC20.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";
import {Panic} from "../utils/Panic.sol";
import {VIPBase} from "./VIPBase.sol";
import {Permit2PaymentAbstract} from "./Permit2Payment.sol";
import {ConfusedDeputy} from "./SettlerErrors.sol";

abstract contract UniswapV2 is Permit2PaymentAbstract, VIPBase {
    using UnsafeMath for uint256;

    // bytes4(keccak256("getReserves()"))
    uint256 private constant UNI_PAIR_RESERVES_CALL_SELECTOR = 0x0902f1ac;
    // bytes4(keccak256("swap(uint256,uint256,address,bytes)"))
    uint256 private constant UNI_PAIR_SWAP_CALL_SELECTOR = 0x022c0d9f;
    // bytes4(keccak256("transfer(address,uint256)"))
    uint256 private constant ERC20_TRANSFER_CALL_SELECTOR = 0xa9059cbb;
    // bytes4(keccak256("balanceOf(address)"))
    uint256 private constant ERC20_BALANCEOF_CALL_SELECTOR = 0x70a08231;

    /// @dev Permit2 address for restricting access
    address private immutable _PERMIT2;
    /// @dev AH address for restricting access
    address private immutable _ALLOWANCE_HOLDER;

    /// @dev Sell a token for another token using UniswapV2.
    function sellToUniswapV2(
        address recipient,
        address sellToken,
        address pool,
        uint8 swapInfo,
        uint256 bips,
        uint256 minBuyAmount
    ) internal {
        // ensure pool isn't Permit2 or AH
        if (isRestrictedTarget(pool)) {
            revert ConfusedDeputy();
        }

        // |7|6|5|4|3|2|1|0| - bit positions in swapInfo (uint8)
        // |0|0|0|0|0|0|F|Z| - Z: zeroForOne flag, F: sellTokenHasFee flag
        bool zeroForOne = (swapInfo & 1) == 1; // Extract the least significant bit (bit 0)
        bool sellTokenHasFee = (swapInfo & 2) >> 1 == 1; // Extract the second least significant bit (bit 1) and shift it right

        // If bips is zero we assume there is no balance, so we skip the update to sellAmount
        // this case can occur if the pool is being chained, in which the balance exists in the pool
        // already
        uint256 sellAmount = 0;
        if (bips != 0) {
            // We don't care about phantom overflow here because reserves are
            // limited to 112 bits. Any token balance that would overflow here would
            // also break UniV2.
            sellAmount = (IERC20(sellToken).balanceOf(address(this)) * bips).unsafeDiv(10_000);
        }
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            let swapCalldata := add(ptr, 0x1c)

            // set up swap call selector and empty callback data
            mstore(ptr, UNI_PAIR_SWAP_CALL_SELECTOR)
            mstore(add(ptr, 0x80), 0x80) // offset to length of data
            mstore(add(ptr, 0xa0), 0) // length of data

            // 28b padding, 4b selector, 32b amount0Out, 32b amount1Out, 32b to, 64b data
            ptr := add(ptr, 0xc0)

            // transfer sellAmount (a non zero amount) of sellToken to the pool
            if sellAmount {
                mstore(ptr, ERC20_TRANSFER_CALL_SELECTOR)
                mstore(add(ptr, 0x20), pool)
                mstore(add(ptr, 0x40), sellAmount)
                if iszero(call(gas(), sellToken, 0, add(ptr, 0x1c), 0x44, 0x00, 0x20)) { bubbleRevert(swapCalldata) }
                if iszero(or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 0x20)), eq(mload(0x00), 1)))) {
                    revert(0, 0)
                }
            }

            // get pool reserves
            let sellReserve
            let buyReserve
            mstore(0x00, UNI_PAIR_RESERVES_CALL_SELECTOR)
            if iszero(staticcall(gas(), pool, 0x1c, 0x04, 0x00, 0x40)) { bubbleRevert(swapCalldata) }
            if lt(returndatasize(), 0x40) { revert(0, 0) }
            {
                let r := shl(5, zeroForOne)
                buyReserve := mload(r)
                sellReserve := mload(xor(0x20, r))
            }

            // TODO handle FoT
            // if the sellToken has a fee on transfer, determine the real sellAmount

            // If the current balance is 0 we assume the funds are in the pool already
            if or(iszero(sellAmount), sellTokenHasFee) {
                // retrieve the sellToken balance of the pool
                mstore(ptr, ERC20_BALANCEOF_CALL_SELECTOR)
                mstore(add(ptr, 0x20), pool)
                if iszero(staticcall(gas(), sellToken, add(ptr, 0x1c), 0x24, 0x00, 0x20)) { bubbleRevert(swapCalldata) }
                if lt(returndatasize(), 0x20) { revert(0, 0) }
                let bal := mload(0x00)

                // determine real sellAmount by comparing pool's sellToken balance to reserve amount
                if lt(bal, sellReserve) {
                    mstore(0x00, 0x4e487b71) // selector for `Panic(uint256)`
                    mstore(0x20, 0x11) // panic code for arithmetic underflow
                    revert(0x1c, 0x24)
                }
                sellAmount := sub(bal, sellReserve)
            }

            // compute buyAmount based on sellAmount and reserves
            let sellAmountWithFee := mul(sellAmount, 997)
            let buyAmount := div(mul(sellAmountWithFee, buyReserve), add(sellAmountWithFee, mul(sellReserve, 1000)))

            // set amount0Out and amount1Out
            {
                // If `zeroForOne`, offset is 0x24, else 0x04
                let offset := add(0x04, mul(zeroForOne, 0x20))
                mstore(add(swapCalldata, offset), buyAmount)
                mstore(add(swapCalldata, xor(0x20, offset)), 0)
            }

            // perform swap at the pool sending bought tokens to the recipient
            mstore(add(swapCalldata, 0x44), and(0xffffffffffffffffffffffffffffffffffffffff, recipient))
            if iszero(call(gas(), pool, 0, swapCalldata, 0xa4, 0, 0)) { bubbleRevert(swapCalldata) }

            // revert with the return data from the most recent call
            function bubbleRevert(p) {
                returndatacopy(p, 0, returndatasize())
                revert(p, returndatasize())
            }
        }
        // sellAmount is the amount sent from the final hop
        if (sellAmount < minBuyAmount) {
            revert TooMuchSlippage(address(0), minBuyAmount, sellAmount);
        }
    }
}

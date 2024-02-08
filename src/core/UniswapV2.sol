// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {IERC20} from "../IERC20.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";
import {Panic} from "../utils/Panic.sol";
import {VIPBase} from "./VIPBase.sol";

abstract contract UniswapV2 is VIPBase {
    using UnsafeMath for uint256;

    // bytes4(keccak256("getReserves()"))
    uint256 private constant UNI_PAIR_RESERVES_CALL_SELECTOR = 0x0902f1ac;
    // bytes4(keccak256("swap(uint256,uint256,address,bytes)"))
    uint256 private constant UNI_PAIR_SWAP_CALL_SELECTOR = 0x022c0d9f;
    // bytes4(keccak256("transfer(address,uint256)"))
    uint256 private constant ERC20_TRANSFER_CALL_SELECTOR = 0xa9059cbb;
    // bytes4(keccak256("balanceOf(address)"))
    uint256 private constant ERC20_BALANCEOF_CALL_SELECTOR = 0x70a08231;

    /// @dev Sell a token for another token using UniswapV2.
    function sellToUniswapV2(
        address recipient,
        address sellToken,
        address buyToken,
        address pool,
        uint256 bips,
        uint256 minBuyAmount
    ) internal {
        // TODO ensure pool isn't Permit2 or AH
        // TODO replace buyToken with zeroForOne + FoT indicator?
        //  | uint8(info) |
        // where first bit of `info` is `sellTokenHasFee` and the rest is zeroForOne
        bool feeOnTransfer = false;

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
            let zeroForOne := lt(sellToken, buyToken)

            // transfer sellAmount (a non zero amount) of sellToken to the pool
            if not(iszero(sellAmount)) {
                mstore(ptr, ERC20_TRANSFER_CALL_SELECTOR)
                mstore(add(ptr, 0x20), pool)
                mstore(add(ptr, 0x40), sellAmount)
                if iszero(call(gas(), sellToken, 0, add(ptr, 0x1c), 0x44, ptr, 0x20)) { bubbleRevert(swapCalldata) }
                if iszero(or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 0x20)), eq(mload(ptr), 1)))) {
                    revert(0, 0)
                }
            }

            // get pool reserves
            let sellReserve
            let buyReserve
            mstore(ptr, UNI_PAIR_RESERVES_CALL_SELECTOR)
            if iszero(staticcall(gas(), pool, add(ptr, 0x1c), 0x04, ptr, 0x40)) { bubbleRevert(swapCalldata) }
            if lt(returndatasize(), 0x40) { revert(0, 0) }
            switch zeroForOne
            case 0 {
                sellReserve := mload(add(ptr, 32))
                buyReserve := mload(ptr)
            }
            default {
                sellReserve := mload(ptr)
                buyReserve := mload(add(ptr, 32))
            }

            // TODO handle FoT
            // if the sellToken has a fee on transfer, determine the real sellAmount

            // If the current balance is 0 we assume the funds are in the pool already
            if or(iszero(sellAmount), feeOnTransfer) {
                // retrieve the sellToken balance of the pool
                mstore(ptr, ERC20_BALANCEOF_CALL_SELECTOR)
                mstore(add(ptr, 0x20), pool)
                if iszero(staticcall(gas(), sellToken, add(ptr, 0x1c), 0x24, ptr, 0x20)) { bubbleRevert(swapCalldata) }
                if lt(returndatasize(), 0x20) { revert(0, 0) }
                let bal := mload(ptr)

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
            switch zeroForOne
            case 0 {
                mstore(add(swapCalldata, 0x04), buyAmount)
                mstore(add(swapCalldata, 0x24), 0)
            }
            default {
                mstore(add(swapCalldata, 0x04), 0)
                mstore(add(swapCalldata, 0x24), buyAmount)
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
            revert TooMuchSlippage(buyToken, minBuyAmount, sellAmount);
        }
    }
}

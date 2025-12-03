// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {Panic} from "../utils/Panic.sol";
import {revertTooMuchSlippage} from "./SettlerErrors.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {Ternary} from "../utils/Ternary.sol";
import {SettlerAbstract} from "../SettlerAbstract.sol";

interface IUniV2Pair {
    function token0() external view returns (address);

    function token1() external view returns (address);

    function getReserves() external view returns (uint112, uint112, uint32);

    function swap(uint256, uint256, address, bytes calldata) external;
}

library fastUniswapV2Pool {
    using Ternary for bool;

    function fastGetReserves(address pool, bool zeroForOne)
        internal
        view
        returns (uint256 sellReserve, uint256 buyReserve)
    {
        assembly ("memory-safe") {
            mstore(0x00, 0x0902f1ac) // selector for `getReserves()`
            if iszero(staticcall(gas(), pool, 0x1c, 0x04, 0x00, 0x40)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            if lt(returndatasize(), 0x40) { revert(0x00, 0x00) }
            let r := shl(0x05, zeroForOne)
            buyReserve := mload(r)
            sellReserve := mload(xor(0x20, r))
        }
    }

    function fastToken0or1(address pool, bool zeroForOne) internal view returns (IERC20 token) {
        // selector for `token1()` or `token0()`
        uint256 selector = zeroForOne.ternary(uint256(0xd21220a7), uint256(0x0dfe1681));
        assembly ("memory-safe") {
            mstore(0x00, selector)
            if iszero(staticcall(gas(), pool, 0x1c, 0x04, 0x00, 0x20)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            token := mload(0x00)
            if or(gt(0x20, returndatasize()), shr(0xa0, token)) { revert(0x00, 0x00) }
        }
    }

    function fastSwap(address pool, bool zeroForOne, uint256 buyAmount, address recipient) internal {
        assembly ("memory-safe") {
            let ptr := mload(0x40)

            mstore(ptr, 0x022c0d9f) // selector for `swap(uint256,uint256,address,bytes)`
            // set amount0Out and amount1Out
            let buyAmountBaseOffset := add(0x20, ptr)
            // If `zeroForOne`, buyAmount offset is 0x40, else 0x20
            let directionOffset := shl(0x05, zeroForOne)
            mstore(add(buyAmountBaseOffset, directionOffset), buyAmount)
            mstore(add(buyAmountBaseOffset, xor(0x20, directionOffset)), 0x00)

            mstore(add(0x60, ptr), and(0xffffffffffffffffffffffffffffffffffffffff, recipient))
            mstore(add(0x80, ptr), 0x80) // offset to length of data
            mstore(add(0xa0, ptr), 0x00) // length of data

            // perform swap at the pool sending bought tokens to the recipient
            if iszero(call(gas(), pool, 0x00, add(0x1c, ptr), 0xa4, 0x00, 0x00)) {
                let ptr_ := mload(0x40)
                returndatacopy(ptr_, 0x00, returndatasize())
                revert(ptr_, returndatasize())
            }
        }
    }
}

abstract contract UniswapV2 is SettlerAbstract {
    using SafeTransferLib for IERC20;
    using fastUniswapV2Pool for address;

    /// @dev Sell a token for another token using UniswapV2.
    function sellToUniswapV2(
        address recipient,
        address sellToken,
        uint256 bps,
        address pool,
        uint24 swapInfo,
        uint256 minBuyAmount
    ) internal {
        // Preventing calls to Permit2 or AH is not explicitly required as neither of these contracts implement the `swap` nor `transfer` selector

        // |7|6|5|4|3|2|1|0| - bit positions in swapInfo (uint8)
        // |0|0|0|0|0|0|F|Z| - Z: zeroForOne flag, F: sellTokenHasFee flag
        bool zeroForOne = (swapInfo & 1) == 1; // Extract the least significant bit (bit 0)
        bool sellTokenHasFee = (swapInfo & 2) >> 1 == 1; // Extract the second least significant bit (bit 1) and shift it right
        uint256 feeBps = swapInfo >> 8;

        uint256 sellAmount;
        uint256 buyAmount;
        // If bps is zero we assume there are no funds within this contract, skip the updating sellAmount.
        // This case occurs if the pool is being chained, in which the funds have been sent directly to the pool
        if (bps != 0) {
            // We don't care about phantom overflow here because reserves are
            // limited to 112 bits. Any token balance that would overflow here would
            // also break UniV2.
            // It is *possible* to set `bps` above the basis and therefore
            // cause an overflow on this multiplication. However, `bps` is
            // passed as authenticated calldata, so this is a GIGO error that we
            // do not attempt to fix.
            unchecked {
                sellAmount = IERC20(sellToken).fastBalanceOf(address(this)) * bps / BASIS;
            }
            IERC20(sellToken).safeTransfer(address(pool), sellAmount);
        }
        (uint256 sellReserve, uint256 buyReserve) = fastUniswapV2Pool.fastGetReserves(pool, zeroForOne);
        if (sellAmount == 0 || sellTokenHasFee) {
            uint256 bal = IERC20(sellToken).fastBalanceOf(pool);
            sellAmount = bal - sellReserve;
        }
        unchecked {
            uint256 sellAmountWithFee = sellAmount * (10000 - feeBps);
            buyAmount = (sellAmountWithFee * buyReserve) / (sellAmountWithFee + sellReserve * 10000);
        }
        if (buyAmount < minBuyAmount) {
            revertTooMuchSlippage(pool.fastToken0or1(zeroForOne), minBuyAmount, buyAmount);
        }
        pool.fastSwap(zeroForOne, buyAmount, recipient);
    }
}

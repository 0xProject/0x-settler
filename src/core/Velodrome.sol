// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";
import {FullMath} from "../vendor/FullMath.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {TooMuchSlippage} from "./SettlerErrors.sol";
import {Panic} from "../utils/Panic.sol";

import {SettlerAbstract} from "../SettlerAbstract.sol";

interface IVelodromePair {
    function metadata()
        external
        view
        returns (
            uint256 basis0,
            uint256 basis1,
            uint256 reserve0,
            uint256 reserve1,
            bool stable,
            IERC20 token0,
            IERC20 token1
        );
    function swap(uint256 amount0Out, uint256 amount1Out, address to, bytes calldata data) external;
}

abstract contract Velodrome is SettlerAbstract {
    using UnsafeMath for uint256;
    using FullMath for uint256;
    using SafeTransferLib for IERC20;

    uint256 internal constant _VELODROME_NEWTON_BASIS = 1 ether * 1 gwei;
    uint256 internal constant _VELODROME_NEWTON_EPS = _VELODROME_NEWTON_BASIS / 2 ether;

    // This is the `k = x^3 * y + y^3 * x` constant function
    function _k(uint256 x, uint256 y) internal pure returns (uint256) {
        unchecked {
            return _k(x, y, x * x / _VELODROME_NEWTON_BASIS);
        }
    }

    function _k(uint256 x, uint256 y, uint256 x_squared) private pure returns (uint256) {
        unchecked {
            return _k(x, y, x_squared, y * y / _VELODROME_NEWTON_BASIS);
        }
    }

    function _k(uint256 x, uint256 y, uint256 x_squared, uint256 y_squared) private pure returns (uint256) {
        unchecked {
            return (x * y / _VELODROME_NEWTON_BASIS).unsafeMulDiv(x_squared + y_squared, _VELODROME_NEWTON_BASIS);
        }
    }

    // For numerically approximating a solution to the `k = x^3 * y + y^3 * x` constant function
    // using Newton-Raphson, this is `∂k/∂y = 3 * x * y^2 + x^3`.
    function _d(uint256 y, uint256 three_x0, uint256 x0_cubed) private pure returns (uint256) {
        unchecked {
            return _d(y, three_x0, x0_cubed, y * y / _VELODROME_NEWTON_BASIS);
        }
    }

    function _d(uint256, uint256 three_x0, uint256 x0_cubed, uint256 y_squared) private pure returns (uint256) {
        unchecked {
            return y_squared * three_x0 / _VELODROME_NEWTON_BASIS + x0_cubed;
        }
    }

    error NotConverged();

    // Using Newton-Raphson iterations, compute the smallest `new_y` such that `_k(x0, new_y) >=
    // xy`. As a function of `y`, we find the root of `_k(x0, y) - xy`.
    function _get_y(uint256 x0, uint256 xy, uint256 y) internal pure returns (uint256) {
        unchecked {
            uint256 three_x0 = 3 * x0;
            uint256 x0_squared = x0 * x0 / _VELODROME_NEWTON_BASIS;
            uint256 x0_cubed = x0_squared * x0 / _VELODROME_NEWTON_BASIS;
            for (uint256 i; i < 255; i++) {
                uint256 y_squared = y * y / _VELODROME_NEWTON_BASIS;
                uint256 k = _k(x0, y, x0_squared, y_squared);
                uint256 d = _d(y, three_x0, x0_cubed, y_squared);
                if (k < xy) {
                    uint256 dy = (xy - k).unsafeMulDiv(_VELODROME_NEWTON_BASIS, d);
                    y += dy;
                    if (dy < _VELODROME_NEWTON_EPS) {
                        return y + (_VELODROME_NEWTON_EPS - 1);
                    }
                } else {
                    uint256 dy = (k - xy).unsafeMulDiv(_VELODROME_NEWTON_BASIS, d);
                    y -= dy;
                    if (dy < _VELODROME_NEWTON_EPS) {
                        return y + (_VELODROME_NEWTON_EPS - 1);
                    }
                }
            }
            revert NotConverged();
        }
    }

    function sellToVelodrome(address recipient, uint256 bps, IVelodromePair pair, uint24 swapInfo, uint256 minAmountOut)
        internal
    {
        // Preventing calls to Permit2 or AH is not explicitly required as neither of these contracts implement the `swap` nor `transfer` selector

        // |7|6|5|4|3|2|1|0| - bit positions in swapInfo (uint8)
        // |0|0|0|0|0|0|F|Z| - Z: zeroForOne flag, F: sellTokenHasFee flag
        bool zeroForOne = (swapInfo & 1) == 1; // Extract the least significant bit (bit 0)
        bool sellTokenHasFee = (swapInfo & 2) >> 1 == 1; // Extract the second least significant bit (bit 1) and shift it right
        uint256 feeBps = swapInfo >> 8;

        (
            uint256 sellBasis,
            uint256 buyBasis,
            uint256 sellReserve,
            uint256 buyReserve,
            bool stable,
            IERC20 sellToken,
            IERC20 buyToken
        ) = pair.metadata();
        assert(stable);
        if (!zeroForOne) {
            (sellBasis, buyBasis, sellReserve, buyReserve, sellToken, buyToken) =
                (buyBasis, sellBasis, buyReserve, sellReserve, buyToken, sellToken);
        }

        uint256 buyAmount;
        unchecked {
            // Compute sell amount in native units
            uint256 sellAmount;
            if (bps != 0) {
                // It must be possible to cube the sell token balance of the pool, otherwise it
                // will revert with an overflow. Therefore, it can't be so large that multiplying by
                // a "reasonable" `bps` value could overflow. We don't care to protect against
                // unreasonable `bps` values because that just means the taker is griefing themself.
                sellAmount = (sellToken.balanceOf(address(this)) * bps).unsafeDiv(BASIS);
            }
            if (sellAmount != 0) {
                sellToken.safeTransfer(address(pair), sellAmount);
            }
            if (sellAmount == 0 || sellTokenHasFee) {
                sellAmount = sellToken.balanceOf(address(pair)) - sellReserve;
            }
            // Apply the fee
            sellAmount -= sellAmount * feeBps / 10_000; // can't overflow

            // Convert everything from native units to `_VELODROME_NEWTON_BASIS`
            sellReserve = (sellReserve * _VELODROME_NEWTON_BASIS).unsafeDiv(sellBasis);
            buyReserve = (buyReserve * _VELODROME_NEWTON_BASIS).unsafeDiv(buyBasis);
            sellAmount = (sellAmount * _VELODROME_NEWTON_BASIS).unsafeDiv(sellBasis);

            // Check for overflow
            if (buyReserve > 1 ether * _VELODROME_NEWTON_BASIS) {
                Panic.panic(Panic.ARITHMETIC_OVERFLOW);
            }
            if (sellAmount + sellReserve > 1 ether * _VELODROME_NEWTON_BASIS) {
                Panic.panic(Panic.ARITHMETIC_OVERFLOW);
            }

            // Solve the constant function numerically to get `buyAmount` from `sellAmount`
            uint256 k = _k(sellReserve, buyReserve);
            buyAmount = buyReserve - _get_y(sellAmount + sellReserve, k, buyReserve);

            // Convert `buyAmount` from `_VELODROME_NEWTON_BASIS` to native units
            buyAmount = buyAmount * buyBasis / _VELODROME_NEWTON_BASIS;
        }
        if (buyAmount < minAmountOut) {
            revert TooMuchSlippage(sellToken, minAmountOut, buyAmount);
        }

        {
            (uint256 buyAmount0, uint256 buyAmount1) = zeroForOne ? (uint256(0), buyAmount) : (buyAmount, uint256(0));
            pair.swap(buyAmount0, buyAmount1, recipient, new bytes(0));
        }
    }
}

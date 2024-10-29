// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";
import {FullMath} from "../vendor/FullMath.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {TooMuchSlippage} from "./SettlerErrors.sol";
import {uint512, tmp} from "../utils/512Math.sol";
import {FreeMemory} from "../utils/FreeMemory.sol";

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

abstract contract Velodrome is SettlerAbstract, FreeMemory {
    using UnsafeMath for uint256;
    using FullMath for uint256;
    using SafeTransferLib for IERC20;

    // This is the basis used for token balances.
    uint256 internal constant _VELODROME_TOKEN_BASIS = 1 ether;

    // The maximum balance in the AMM's implementation of `k` is `b` such that
    // `b * b / 1 ether * b / 1 ether * b` does not overflow. This that
    // quantity, `b`.
    uint256 internal constant _VELODROME_MAX_BALANCE = 18446744073709551616000000000;

    function _k(uint512 memory r, uint256 x, uint256 x_basis, uint256 y, uint256 y_basis) internal pure {
        unchecked {
            r.omul(x * x, y_basis * y_basis).iadd(tmp().omul(y * y, x_basis * x_basis)).imul(x * y);
        }
    }

    function _d(uint512 memory r, uint256 x, uint256 x_basis, uint256 y, uint256 y_basis) internal pure {
        unchecked {
            r.omul(x * x, y_basis * y_basis).iadd(tmp().omul(3 * y * y, x_basis * x_basis)).imul(x);
        }
    }

    function nrStep(uint512 memory k_new, uint512 memory k_orig, uint256 x, uint256 x_basis, uint256 y, uint256 y_basis) private view DANGEROUS_freeMemory returns (uint256 new_y) {
        unchecked {
            uint512 memory d;
            _k(k_new, x, x_basis, y, y_basis);
            _d(d, x, x_basis, y, y_basis);
            if (k_new.lt(k_orig)) {
                new_y = y + tmp().osub(k_orig, k_new).div(d);
            } else {
                new_y = y - tmp().osub(k_new, k_orig).div(d);
            }
        }
    }

    error NotConverged();

    // Using Newton-Raphson iterations, compute the smallest `new_y` such that `_k(x + dx, new_y) >=
    // _k(x, y)`. As a function of `new_y`, we find the root of `_k(x + dx, new_y) - _k(x, y)`.
    function _get_y(uint256 x, uint256 dx, uint256 x_basis, uint256 y, uint256 y_basis) internal view DANGEROUS_freeMemory returns (uint256) {
        uint512 memory k_orig;
        _k(k_orig, x, x_basis, y, y_basis);
        uint512 memory k_new;

        uint256 max = _VELODROME_MAX_BALANCE * y_basis / 1 ether;

        // Now that we have `k` computed, we offset `x` to account for the sell amount and use
        // the constant-product formula to compute an initial estimate for `y`.
        x += dx;
        y -= (dx * y).unsafeDiv(x);

        for (uint256 i; i < 255; i++) {
            uint256 new_y = nrStep(k_new, k_orig, x, x_basis, y, y_basis);
            if (new_y == y) {
                if (k_new.ge(k_orig)) {
                    return new_y;
                }
                new_y++;
                _k(k_new, x, x_basis, new_y, y_basis);
                if (k_new.ge(k_orig)) {
                    return new_y;
                }
                new_y++;
            }
            if (new_y > max) {
                y = max;
            } else {
                y = new_y;
            }
        }
        revert NotConverged();
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
                // It must be possible to square the sell token balance of the pool, otherwise it
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

            // Apply the fee in native units
            sellAmount -= sellAmount * feeBps / 10_000; // can't overflow

            // Solve the constant function numerically to get `buyAmount` from `sellAmount`
            buyAmount = buyReserve - _get_y(sellReserve, sellAmount, sellBasis, buyReserve, buyBasis);
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

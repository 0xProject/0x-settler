// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";
import {FastLogic} from "../utils/FastLogic.sol";
import {FullMath} from "../vendor/FullMath.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {revertTooMuchSlippage, NotConverged} from "./SettlerErrors.sol";
import {uint512, tmp, alloc} from "../utils/512Math.sol";

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
    using FastLogic for bool;
    using FullMath for uint256;
    using SafeTransferLib for IERC20;

    // This is the basis used for token balances.
    uint256 internal constant _VELODROME_TOKEN_BASIS = 1 ether;

    // The maximum balance in the AMM's implementation of `k` is `b` such that `b * b / 1 ether * b
    // / 1 ether * b * 2` does not overflow. This that quantity, `b`.
    uint256 internal constant _VELODROME_MAX_BALANCE = 15511800964685064948225197537;

    // k = x³y+y³x
    function _k(uint512 r, uint256 x, uint256 x_basis, uint256 y, uint256 y_basis) internal pure {
        unchecked {
            r.omul(x * x, y_basis * y_basis).iadd(tmp().omul(y * y, x_basis * x_basis)).imul(x * y);
        }
    }

    function _k_alt(uint512 r, uint256 x, uint256 xbasis_squared, uint256 y, uint256 ybasis_squared) private pure {
        unchecked {
            r.omul(x * x, ybasis_squared).iadd(tmp().omul(y * y, xbasis_squared)).imul(x * y);
        }
    }

    function _k(uint512 r, uint256 x, uint512 x_ybasis_squared, uint256 xbasis_squared, uint256 y) private pure {
        unchecked {
            r.oadd(x_ybasis_squared, tmp().omul(y * y, xbasis_squared)).imul(x * y);
        }
    }

    function _k(uint512 r, uint256 x, uint512 x_ybasis_squared, uint256 y, uint512 y_xbasis_squared) private pure {
        unchecked {
            r.oadd(x_ybasis_squared, y_xbasis_squared).imul(x * y);
        }
    }

    // d = ∂k/∂y = 3*x*y² + x³
    function _d(uint512 r, uint256 x, uint256 x_basis, uint256 y, uint256 y_basis) internal pure {
        unchecked {
            r.omul(x * x, y_basis * y_basis).iadd(tmp().omul(3 * y * y, x_basis * x_basis)).imul(x);
        }
    }

    function _d(uint512 r, uint256 x, uint512 x_ybasis_squared, uint512 y_xbasis_squared) private pure {
        unchecked {
            r.oadd(x_ybasis_squared, tmp().omul(y_xbasis_squared, 3)).imul(x);
        }
    }

    function nrStep(
        // output parameters
        uint512 k_new,
        uint512 d,
        // input parameters
        uint512 k_orig,
        uint256 x,
        uint512 x_ybasis_squared,
        uint256 xbasis_squared,
        uint256 y,
        // scratch space
        uint512 y_xbasis_squared
    ) private view returns (uint256 new_y) {
        unchecked {
            y_xbasis_squared.omul(y * y, xbasis_squared);
            _k(k_new, x, x_ybasis_squared, y, y_xbasis_squared);
            _d(d, x, x_ybasis_squared, y_xbasis_squared);
            if (k_new < k_orig) {
                new_y = y + _div512to256(tmp().osub(k_orig, k_new), d);
            } else {
                new_y = y - _div512to256(tmp().osub(k_new, k_orig), d);
            }
        }
    }

    // Using Newton-Raphson iterations, compute the smallest `new_y` such that `k(x + dx, new_y) >=
    // k(x, y)`. As a function of `new_y`, we find the root of `k(x + dx, new_y) - k(x, y)`.
    function _get_y(uint256 x, uint256 dx, uint256 x_basis, uint256 y, uint256 y_basis)
        internal
        view
        returns (uint256)
    {
        unchecked {
            uint256 y_max = _VELODROME_MAX_BALANCE * y_basis / _VELODROME_TOKEN_BASIS;

            // The values for `x_basis` and `y_basis` don't need to be exactly correct, they only
            // need to be correct relative to each other. Because we know that they are both powers
            // of 10 (computed as `10 ** decimals()`), one is a multiple of the other. By dividing
            // the greater by the lesser, we set at least one of them to 1. This also increases the
            // chances that we can take the more gas-optimized paths inside the 512-bit division
            // routine.
            if (x_basis > y_basis) {
                x_basis /= y_basis;
                y_basis = 1;
            } else {
                y_basis /= x_basis;
                x_basis = 1;
            }

            // Because uint512's live in memory, we preallocate them here to avoid allocating in the loop
            uint512 k_orig = alloc(); // the target value for `k` after swapping
            uint512 k_new = alloc(); // the current value of `k`, for this iteration
            uint512 x_ybasis_squared = alloc(); // x² * y_basis²; cached
            uint512 y_xbasis_squared = alloc(); // y² * x_basis²; updated on each loop
            uint512 d = alloc(); // ∂k/∂y = 3*x*y² + x³
            uint256 xbasis_squared;
            {
                xbasis_squared = x_basis * x_basis;
                uint256 ybasis_squared = y_basis * y_basis;
                _k_alt(k_orig, x, xbasis_squared, y, ybasis_squared);

                // Now that we have `k` computed, we offset `x` to account for the sell amount and
                // use the constant-product formula to compute an initial estimate for `y`.
                x += dx;
                y -= (dx * y).unsafeDiv(x);

                // This value remains constant throughout the iterations, so we precompute
                x_ybasis_squared.omul(x * x, ybasis_squared);
            }

            for (uint256 i; i < 255; i++) {
                uint256 new_y = nrStep(k_new, d, k_orig, x, x_ybasis_squared, xbasis_squared, y, y_xbasis_squared);
                if (new_y == y) {
                    if (k_new >= k_orig) {
                        _k(k_new, x, x_ybasis_squared, xbasis_squared, new_y - 1);
                        if (k_new < k_orig) {
                            return new_y;
                        }
                        new_y--;
                    } else {
                        new_y++;
                        _k(k_new, x, x_ybasis_squared, xbasis_squared, new_y);
                        if (k_new >= k_orig) {
                            return new_y;
                        }
                        new_y++;
                    }
                }
                if (new_y > y_max) {
                    y = y_max;
                } else {
                    y = new_y;
                }
            }
        }
        assembly ("memory-safe") {
            mstore(0x00, 0x481b61af) // selector for `NotConverged()`
            revert(0x1c, 0x04)
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
                // It must be possible to square the sell token balance of the pool, otherwise it
                // will revert with an overflow. Therefore, it can't be so large that multiplying by
                // a "reasonable" `bps` value could overflow. We don't care to protect against
                // unreasonable `bps` values because that just means the taker is griefing themself.
                sellAmount = (sellToken.fastBalanceOf(address(this)) * bps).unsafeDiv(BASIS);
            }
            if (sellAmount != 0) {
                sellToken.safeTransfer(address(pair), sellAmount);
            }
            if ((sellAmount == 0).or(sellTokenHasFee)) {
                sellAmount = sellToken.fastBalanceOf(address(pair)) - sellReserve;
            }

            // Apply the fee in native units
            sellAmount -= sellAmount * feeBps / 10_000; // can't overflow

            // Clamp the precision in which we work to 1e18. This makes sure that we're quantizing
            // (rounding down) the same as the AMM and it ensures that we don't encounter overflow
            // in scenarious where the AMM wouldn't.
            if (sellBasis > _VELODROME_TOKEN_BASIS) {
                uint256 scaleDown = sellBasis.unsafeDiv(_VELODROME_TOKEN_BASIS);
                sellAmount = sellAmount.unsafeDiv(scaleDown);
                sellReserve = sellReserve.unsafeDiv(scaleDown);
                sellBasis = _VELODROME_TOKEN_BASIS;
            }

            if (buyBasis > _VELODROME_TOKEN_BASIS) {
                // Internally to the AMM, the quantum is `scaleDown`, so we ensure that our solution
                // lies exactly on that quantum.
                uint256 scaleDown = buyBasis.unsafeDiv(_VELODROME_TOKEN_BASIS);
                buyReserve = buyReserve.unsafeDiv(scaleDown);

                // Solve the constant function numerically to get `buyAmount` from `sellAmount`,
                // with a quantum of `scaleDown` in the buy token's native units
                buyAmount = buyReserve - _get_y(sellReserve, sellAmount, sellBasis, buyReserve, _VELODROME_TOKEN_BASIS);
                // Correct for the fact that the implementation in the pool is inexact and sometimes
                // requires a smaller buy amount to be satisfied.
                buyAmount--;

                // Scale the `buyAmount` back up to the buy token's native units
                buyAmount *= scaleDown;
            } else {
                // Solve the constant function numerically to get `buyAmount` from `sellAmount`
                buyAmount = buyReserve - _get_y(sellReserve, sellAmount, sellBasis, buyReserve, buyBasis);
                // Correct for the fact that the implementation in the pool is inexact and sometimes
                // requires a smaller buy amount to be satisfied.
                buyAmount--;
            }
        }

        if (buyAmount < minAmountOut) {
            revertTooMuchSlippage(sellToken, minAmountOut, buyAmount);
        }

        {
            (uint256 buyAmount0, uint256 buyAmount1) = zeroForOne ? (uint256(0), buyAmount) : (buyAmount, uint256(0));
            pair.swap(buyAmount0, buyAmount1, recipient, new bytes(0));
        }
    }
}

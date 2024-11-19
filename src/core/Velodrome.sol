// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";
import {FullMath} from "../vendor/FullMath.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {TooMuchSlippage, NotConverged} from "./SettlerErrors.sol";
//import {Panic} from "../utils/Panic.sol";

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

    // This is the basis used for token balances. The original token may have fewer decimals, in
    // which case we scale up by the appropriate factor to give this basis.
    uint256 internal constant _VELODROME_TOKEN_BASIS = 1 ether;

    // When computing `k`, to minimize rounding error, we use a significantly larger basis. This
    // also allows us to save work in the Newton-Raphson step because dividing a quantity with this
    // basis by a quantity with `_VELODROME_TOKEN_BASIS` basis gives that same
    // `_VELODROME_TOKEN_BASIS` basis. Convenient *and* accurate.
    uint256 private constant _VELODROME_INTERNAL_BASIS = _VELODROME_TOKEN_BASIS * _VELODROME_TOKEN_BASIS;

    uint256 private constant _VELODROME_INTERNAL_TO_TOKEN_RATIO = _VELODROME_INTERNAL_BASIS / _VELODROME_TOKEN_BASIS;

    // When computing `d` we need to compute the cube of a token quantity and format the result with
    // `_VELODROME_TOKEN_BASIS`. In order to avoid overflow, we must divide the squared token
    // quantity by this before multiplying again by the token quantity. Setting this value as small
    // as possible preserves precision. This gives a result in an awkward basis, but we'll correct
    // that with `_VELODROME_CUBE_STEP_BASIS` after the cubing
    uint256 private constant _VELODROME_SQUARE_STEP_BASIS = 32233524;

    // After squaring a token quantity (in `_VELODROME_TOKEN_BASIS`), we need to multiply again by a
    // token quantity and then divide out the awkward basis to get back to
    // `_VELODROME_TOKEN_BASIS`. This constant is what gets us back to the original token quantity
    // basis. `_VELODROME_TOKEN_BASIS * _VELODROME_TOKEN_BASIS / _VELODROME_SQUARE_STEP_BASIS *
    // _VELODROME_TOKEN_BASIS / _VELODROME_CUBE_STEP_BASIS == _VELODROME_TOKEN_BASIS`
    uint256 private constant _VELODROME_CUBE_STEP_BASIS = 31023601390899735319042373399;

    // The maximum balance in the AMM's implementation of `k` is `b` such that `b * b / 1 ether * b
    // / 1 ether * b * 2` does not overflow. This that quantity, `b`.
    uint256 internal constant _VELODROME_MAX_BALANCE = 15511800964685064948225197537;

    // This is the `k = x^3 * y + y^3 * x` constant function. Unlike the original formulation, the
    // result has a basis of `_VELODROME_INTERNAL_BASIS` instead of `_VELODROME_TOKEN_BASIS`
    function _k(uint256 x, uint256 y) private pure returns (uint256) {
        unchecked {
            return _k(x, y, x * x);
        }
    }

    function _k(uint256 x, uint256 y, uint256 x_squared) private pure returns (uint256) {
        unchecked {
            return _k(x, y, x_squared, y * y);
        }
    }

    function _k(uint256 x, uint256 y, uint256 x_squared, uint256 y_squared) private pure returns (uint256) {
        unchecked {
            return (x * y).unsafeMulDivAlt(x_squared + y_squared, _VELODROME_INTERNAL_BASIS);
        }
    }

    function _k_compat(uint256 x, uint256 y) internal pure returns (uint256) {
        unchecked {
            return (x * y).unsafeMulDivAlt(x * x + y * y, _VELODROME_INTERNAL_BASIS * _VELODROME_TOKEN_BASIS);
        }
    }

    // For numerically approximating a solution to the `k = x^3 * y + y^3 * x` constant function
    // using Newton-Raphson, this is `∂k/∂y = 3 * x * y^2 + x^3`. The result has a basis of
    // `_VELODROME_TOKEN_BASIS`.
    function _d(uint256 y, uint256 x) private pure returns (uint256) {
        unchecked {
            return _d(y, 3 * x, x * x / _VELODROME_SQUARE_STEP_BASIS * x / _VELODROME_CUBE_STEP_BASIS);
        }
    }

    function _d(uint256 y, uint256 three_x, uint256 x_cubed) private pure returns (uint256) {
        unchecked {
            return _d(y, three_x, x_cubed, y * y / _VELODROME_SQUARE_STEP_BASIS);
        }
    }

    function _d(uint256, uint256 three_x, uint256 x_cubed, uint256 y_squared) private pure returns (uint256) {
        unchecked {
            return y_squared * three_x / _VELODROME_CUBE_STEP_BASIS + x_cubed;
        }
    }

    // Using Newton-Raphson iterations, compute the smallest `new_y` such that `_k(x + dx, new_y) >=
    // _k(x, y)`. As a function of `new_y`, we find the root of `_k(x + dx, new_y) - _k(x, y)`.
    function _get_y(uint256 x, uint256 dx, uint256 y) internal pure returns (uint256) {
        unchecked {
            uint256 k_orig = _k(x, y);
            // `k_orig` has a basis much greater than is actually required for correctness. To
            // achieve wei-level accuracy, we perform our final comparisons agains `k_target`
            // instead, which has the same precision as the AMM itself.
            uint256 k_target = k_orig / _VELODROME_INTERNAL_TO_TOKEN_RATIO;

            // Now that we have `k` computed, we offset `x` to account for the sell amount and use
            // the constant-product formula to compute an initial estimate for `y`.
            x += dx;
            y -= (dx * y).unsafeDiv(x);

            // These intermediate values do not change throughout the Newton-Raphson iterations, so
            // precomputing and caching them saves us gas.
            uint256 three_x = 3 * x;
            uint256 x_squared_raw = x * x;
            uint256 x_cubed = x_squared_raw / _VELODROME_SQUARE_STEP_BASIS * x / _VELODROME_CUBE_STEP_BASIS;

            for (uint256 i; i < 255; i++) {
                uint256 y_squared_raw = y * y;
                uint256 k = _k(x, y, x_squared_raw, y_squared_raw);
                uint256 d = _d(y, three_x, x_cubed, y_squared_raw / _VELODROME_SQUARE_STEP_BASIS);

                if (k < k_orig) {
                    uint256 dy = (k_orig - k).unsafeDiv(d);
                    // there are two cases where `dy == 0`
                    // case 1: The `y` is converged and we find the correct answer
                    // case 2: `_d(y, x)` is too large compare to `(k_orig - k)` and the rounding
                    //         error screwed us.
                    //         In this case, we need to increase `y` by 1
                    if (dy == 0) {
                        uint256 k_next = _k(x, y + 1, x_squared_raw) / _VELODROME_INTERNAL_TO_TOKEN_RATIO;
                        if (k_next >= k_target) {
                            // If `_k(x, y + 1) >= k_orig`, then we are close to the correct answer.
                            // There's no closer answer than `y + 1`
                            return y + 1;
                        }
                        // `y + 1` does not give us the condition `k >= k_orig`, so we have to do at
                        // least 1 more iteration to find a satisfactory `y` value
                        dy = 2;
                    }
                    y += dy;
                    if (y > _VELODROME_MAX_BALANCE) {
                        y = _VELODROME_MAX_BALANCE;
                    }
                } else {
                    uint256 dy = (k - k_orig).unsafeDiv(d);
                    if (dy == 0) {
                        if (k / _VELODROME_INTERNAL_TO_TOKEN_RATIO == k_target) {
                            // Likewise, if `k == k_orig`, we found the correct answer.
                            return y;
                        }
                        uint256 k_next = _k(x, y - 1, x_squared_raw) / _VELODROME_INTERNAL_TO_TOKEN_RATIO;
                        if (k_next < k_target) {
                            // If `_k(x, y - 1) < k_orig`, then we are close to the correct answer.
                            // There's no closer answer than `y`
                            // It's worth mentioning that we need to find `y` where `_k(x, y) >=
                            // k_orig`
                            // As a result, we can't return `y - 1` even it's closer to the correct
                            // answer
                            return y;
                        }
                        if (k_next == k_target) {
                            return y - 1;
                        }
                        // It's possible that `y - 1` is the correct answer. To know that, we must
                        // check that `y - 2` gives `k < k_orig`. We must do at least 1 more
                        // iteration to determine this.
                        dy = 2;
                    }
                    y -= dy;
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
                // It must be possible to square the sell token balance of the pool, otherwise it
                // will revert with an overflow. Therefore, it can't be so large that multiplying by
                // a "reasonable" `bps` value could overflow. We don't care to protect against
                // unreasonable `bps` values because that just means the taker is griefing themself.
                sellAmount = (sellToken.fastBalanceOf(address(this)) * bps).unsafeDiv(BASIS);
            }
            if (sellAmount != 0) {
                sellToken.safeTransfer(address(pair), sellAmount);
            }
            if (sellAmount == 0 || sellTokenHasFee) {
                sellAmount = sellToken.fastBalanceOf(address(pair)) - sellReserve;
            }

            // Convert reserves from native units to `_VELODROME_TOKEN_BASIS`
            sellReserve = (sellReserve * _VELODROME_TOKEN_BASIS).unsafeDiv(sellBasis);
            buyReserve = (buyReserve * _VELODROME_TOKEN_BASIS).unsafeDiv(buyBasis);

            // This check is commented because values that are too large will
            // result in reverts inside the pool anyways. We don't need to
            // bother.
            /*
            // Check for overflow
            if (buyReserve > _VELODROME_MAX_BALANCE) {
                Panic.panic(Panic.ARITHMETIC_OVERFLOW);
            }
            if (sellReserve + (sellAmount * _VELODROME_TOKEN_BASIS).unsafeDiv(sellBasis) > _VELODROME_MAX_BALANCE) {
                Panic.panic(Panic.ARITHMETIC_OVERFLOW);
            }
            */

            // Apply the fee in native units
            sellAmount -= sellAmount * feeBps / 10_000; // can't overflow
            // Convert sell amount from native units to `_VELODROME_TOKEN_BASIS`
            sellAmount = (sellAmount * _VELODROME_TOKEN_BASIS).unsafeDiv(sellBasis);

            // Solve the constant function numerically to get `buyAmount` from `sellAmount`
            buyAmount = buyReserve - _get_y(sellReserve, sellAmount, buyReserve);

            // Convert `buyAmount` from `_VELODROME_TOKEN_BASIS` to native units
            buyAmount = buyAmount * buyBasis / _VELODROME_TOKEN_BASIS;
        }
        buyAmount--;
        if (buyAmount < minAmountOut) {
            revert TooMuchSlippage(sellToken, minAmountOut, buyAmount);
        }

        {
            (uint256 buyAmount0, uint256 buyAmount1) = zeroForOne ? (uint256(0), buyAmount) : (buyAmount, uint256(0));
            pair.swap(buyAmount0, buyAmount1, recipient, new bytes(0));
        }
    }
}

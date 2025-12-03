// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {UnsafeMath, Math} from "../utils/UnsafeMath.sol";
import {Panic} from "../utils/Panic.sol";

/// @title Contains 512-bit math functions
/// @notice Facilitates multiplication and division that can have overflow of an intermediate value without any loss of precision
/// @dev Handles "phantom overflow" i.e., allows multiplication and division where an intermediate value overflows 256 bits
/// @dev Credit to Remco Bloemen under MIT license https://xn--2-umb.com/21/muldiv
library FullMath {
    using UnsafeMath for uint256;
    using UnsafeMath for uint8;
    using Math for uint256;
    using Math for bool;

    /// @notice 512-bit multiply [prod1 prod0] = a * b
    /// @param a The multiplicand
    /// @param b The multiplier
    /// @return lo Least significant 256 bits of the product
    /// @return hi Most significant 256 bits of the product
    function fullMul(uint256 a, uint256 b) internal pure returns (uint256 lo, uint256 hi) {
        // Compute the product mod 2**256 and mod 2**256 - 1 then use the Chinese
        // Remainder Theorem to reconstruct the 512 bit result. The result is stored
        // in two 256 variables such that product = prod1 * 2**256 + prod0
        assembly ("memory-safe") {
            let mm := mulmod(a, b, not(0x00))
            lo := mul(a, b)
            hi := sub(sub(mm, lo), lt(mm, lo))
        }
    }

    function fullLt(uint256 a_lo, uint256 a_hi, uint256 b_lo, uint256 b_hi) internal pure returns (bool r) {
        assembly ("memory-safe") {
            r := or(lt(a_hi, b_hi), and(eq(a_hi, b_hi), lt(a_lo, b_lo)))
        }
    }

    /// @notice 512-bit multiply [prod1 prod0] = a * b
    /// @param a The multiplicand
    /// @param b The multiplier
    /// @param denominator The divisor
    /// @return prod0 Least significant 256 bits of the product
    /// @return prod1 Most significant 256 bits of the product
    /// @return remainder Remainder of full-precision division
    function _mulDivSetup(uint256 a, uint256 b, uint256 denominator)
        private
        pure
        returns (uint256 prod0, uint256 prod1, uint256 remainder)
    {
        (prod0, prod1) = fullMul(a, b);
        remainder = a.unsafeMulMod(b, denominator);
    }

    /// @notice 512-bit by 256-bit division.
    /// @param prod0 Least significant 256 bits of the product
    /// @param prod1 Most significant 256 bits of the product
    /// @param denominator The divisor
    /// @param remainder Remainder of full-precision division
    /// @return The 256-bit result
    /// @dev Overflow and division by zero aren't checked and are GIGO errors
    function _mulDivInvert(uint256 prod0, uint256 prod1, uint256 denominator, uint256 remainder)
        private
        pure
        returns (uint256)
    {
        uint256 inv;
        assembly ("memory-safe") {
            // Make division exact by rounding [prod1 prod0] down to a multiple of
            // denominator
            // Subtract 256 bit number from 512 bit number
            prod1 := sub(prod1, gt(remainder, prod0))
            prod0 := sub(prod0, remainder)

            // Factor powers of two out of denominator
            {
                // Compute largest power of two divisor of denominator.
                // Always >= 1.
                let twos := and(sub(0, denominator), denominator)

                // Divide denominator by power of two
                denominator := div(denominator, twos)

                // Divide [prod1 prod0] by the factors of two
                prod0 := div(prod0, twos)
                // Shift in bits from prod1 into prod0. For this we need to flip `twos`
                // such that it is 2**256 / twos.
                // If twos is zero, then it becomes one
                twos := add(div(sub(0, twos), twos), 1)
                prod0 := or(prod0, mul(prod1, twos))
            }

            // Invert denominator mod 2**256
            // Now that denominator is an odd number, it has an inverse modulo 2**256
            // such that denominator * inv = 1 mod 2**256.
            // Compute the inverse by starting with a seed that is correct correct for
            // four bits. That is, denominator * inv = 1 mod 2**4
            inv := xor(mul(3, denominator), 2)

            // Now use Newton-Raphson iteration to improve the precision.
            // Thanks to Hensel's lifting lemma, this also works in modular
            // arithmetic, doubling the correct bits in each step.
            inv := mul(inv, sub(2, mul(denominator, inv))) // inverse mod 2**8
            inv := mul(inv, sub(2, mul(denominator, inv))) // inverse mod 2**16
            inv := mul(inv, sub(2, mul(denominator, inv))) // inverse mod 2**32
            inv := mul(inv, sub(2, mul(denominator, inv))) // inverse mod 2**64
            inv := mul(inv, sub(2, mul(denominator, inv))) // inverse mod 2**128
            inv := mul(inv, sub(2, mul(denominator, inv))) // inverse mod 2**256
        }

        // Because the division is now exact we can divide by multiplying with the
        // modular inverse of denominator. This will give us the correct result
        // modulo 2**256. Since the precoditions guarantee that the outcome is less
        // than 2**256, this is the final result.  We don't need to compute the high
        // bits of the result and prod1 is no longer required.
        unchecked {
            return prod0 * inv;
        }
    }

    /// @notice Calculates a×b÷denominator with full precision then rounds towards 0. Throws if result overflows a uint256 or denominator == 0
    /// @param a The multiplicand
    /// @param b The multiplier
    /// @param denominator The divisor
    /// @return The 256-bit result
    function mulDiv(uint256 a, uint256 b, uint256 denominator) internal pure returns (uint256) {
        (uint256 prod0, uint256 prod1, uint256 remainder) = _mulDivSetup(a, b, denominator);
        // Make sure the result is less than 2**256.
        // Also prevents denominator == 0
        if (denominator <= prod1) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW.unsafeInc(denominator == 0));
        }

        // Handle non-overflow cases, 256 by 256 division
        if (prod1 == 0) {
            return prod0.unsafeDiv(denominator);
        }
        return _mulDivInvert(prod0, prod1, denominator, remainder);
    }

    /// @notice Calculates a×b÷denominator with full precision then rounds towards positive infinity. Throws if result overflows a uint256 or denominator == 0
    /// @param a The multiplicand
    /// @param b The multiplier
    /// @param denominator The divisor
    /// @return The 256-bit result
    function mulDivUp(uint256 a, uint256 b, uint256 denominator) internal pure returns (uint256) {
        (uint256 prod0, uint256 prod1, uint256 remainder) = _mulDivSetup(a, b, denominator);
        // Make sure the result is less than 2**256.
        // Also prevents denominator == 0
        if (denominator <= prod1) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW.unsafeInc(denominator == 0));
        }

        // Handle non-overflow cases, 256 by 256 division
        if (prod1 == 0) {
            return prod0.unsafeDivUp(denominator);
        }
        return _mulDivInvert(prod0, prod1, denominator, remainder).inc(0 < remainder);
    }

    /// @notice Calculates a×b÷denominator with full precision then rounds towards positive infinity. Returns `type(uint256).max` if result overflows a uint256 or denominator == 0
    /// @param a The multiplicand
    /// @param b The multiplier
    /// @param denominator The divisor
    /// @return The 256-bit result
    function saturatingMulDivUp(uint256 a, uint256 b, uint256 denominator) internal pure returns (uint256) {
        (uint256 prod0, uint256 prod1, uint256 remainder) = _mulDivSetup(a, b, denominator);
        uint256 overflow;
        unchecked {
            overflow = (denominator > prod1).toInt() - 1;
        }
        if (prod1 == 0) {
            return prod0.unsafeDivUp(denominator).saturatingAdd(overflow);
        }
        return _mulDivInvert(prod0, prod1, denominator, remainder).inc(0 < remainder).saturatingAdd(overflow);
    }

    /// @notice Calculates a×b÷denominator with full precision then rounds towards 0. Overflowing a uint256 or denominator == 0 are GIGO errors
    /// @param a The multiplicand
    /// @param b The multiplier
    /// @param denominator The divisor
    /// @return The 256-bit result
    function unsafeMulDiv(uint256 a, uint256 b, uint256 denominator) internal pure returns (uint256) {
        (uint256 prod0, uint256 prod1, uint256 remainder) = _mulDivSetup(a, b, denominator);
        // Overflow and zero-division checks are skipped
        // Handle non-overflow cases, 256 by 256 division
        if (prod1 == 0) {
            return prod0.unsafeDiv(denominator);
        }
        return _mulDivInvert(prod0, prod1, denominator, remainder);
    }

    /// @notice Calculates a×b÷denominator with full precision then rounds towards 0. Overflowing a uint256 or denominator == 0 are GIGO errors
    /// @param a The multiplicand
    /// @param b The multiplier
    /// @param denominator The divisor
    /// @dev This is the branchless, straight line version of `unsafeMulDiv`. If we know that `prod1 != 0` this may be faster. Also this gives Solc a better chance to optimize.
    /// @return The 256-bit result
    function unsafeMulDivAlt(uint256 a, uint256 b, uint256 denominator) internal pure returns (uint256) {
        (uint256 prod0, uint256 prod1, uint256 remainder) = _mulDivSetup(a, b, denominator);
        return _mulDivInvert(prod0, prod1, denominator, remainder);
    }

    /// @notice Calculates a×b÷denominator with full precision then rounds towards positive infinity. Overflowing a uint256 or denominator == 0 are GIGO errors
    /// @param a The multiplicand
    /// @param b The multiplier
    /// @param denominator The divisor
    /// @return The 256-bit result
    function unsafeMulDivUp(uint256 a, uint256 b, uint256 denominator) internal pure returns (uint256) {
        (uint256 prod0, uint256 prod1, uint256 remainder) = _mulDivSetup(a, b, denominator);
        // Overflow and zero-division checks are skipped
        // Handle non-overflow cases, 256 by 256 division
        if (prod1 == 0) {
            return prod0.unsafeDivUp(denominator);
        }
        return _mulDivInvert(prod0, prod1, denominator, remainder).unsafeInc(0 < remainder);
    }

    /// @notice Calculates a×b÷denominator with full precision then rounds towards positive infinity. Overflowing a uint256 or denominator == 0 are GIGO errors
    /// @param a The multiplicand
    /// @param b The multiplier
    /// @param denominator The divisor
    /// @dev This is the branchless, straight line version of `unsafeMulDivUp`. If we know that `prod1 != 0` this may be faster. Also this gives Solc a better chance to optimize.
    /// @return The 256-bit result
    function unsafeMulDivUpAlt(uint256 a, uint256 b, uint256 denominator) internal pure returns (uint256) {
        (uint256 prod0, uint256 prod1, uint256 remainder) = _mulDivSetup(a, b, denominator);
        return _mulDivInvert(prod0, prod1, denominator, remainder).unsafeInc(0 < remainder);
    }

    function unsafeMulShift(uint256 a, uint256 b, uint256 s) internal pure returns (uint256 result) {
        assembly ("memory-safe") {
            let mm := mulmod(a, b, not(0x00))
            let prod0 := mul(a, b)
            let prod1 := sub(sub(mm, prod0), lt(mm, prod0))
            result := or(shr(s, prod0), shl(sub(0x100, s), prod1))
        }
    }

    function unsafeMulShiftUp(uint256 a, uint256 b, uint256 s) internal pure returns (uint256 result) {
        assembly ("memory-safe") {
            let mm := mulmod(a, b, not(0x00))
            let prod0 := mul(a, b)
            let prod1 := sub(sub(mm, prod0), lt(mm, prod0))
            let s_ := sub(0x100, s)
            result := or(shr(s, prod0), shl(s_, prod1))
            result := add(lt(0x00, shl(s_, prod0)), result)
        }
    }
}

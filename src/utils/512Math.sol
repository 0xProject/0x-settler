// SPDX-License-Identifier: MIT
pragma solidity =0.8.25;

import {Panic} from "./Panic.sol";
import {UnsafeMath} from "./UnsafeMath.sol";

/// The type uint512 behaves as if it were declared as
///     struct uint512 {
///         uint512 hi;
///         uint512 lo;
///     }
/// However, returning `memory` references from internal functions is impossible
/// to do efficiently, especially when the functions are small and are called
/// frequently. Therefore, we assume direct control over memory allocation using
/// the functions `tmp()` and `alloc()` defined below.
///
/// MAKING A DECLARATION OF THE FOLLOWING FORM WILL CAUSE UNEXPECTED BEHAVIOR:
///     uint512 x;
/// INSTEAD OF DOING THAT, YOU MUST USE `alloc()`, LIKE THIS:
///     uint512 x = alloc();
/// IF YOU REALLY WANTED TO DO THAT (ADVANCED USAGE) THEN FOR CLARITY, WRITE THE
/// FOLLOWING:
///     uint512 x = tmp();
type uint512 is bytes32;

function alloc() pure returns (uint512 r) {
    assembly ("memory-safe") {
        r := mload(0x40)
        mstore(0x40, add(0x40, r))
    }
}

function tmp() pure returns (uint512 r) {}

library Lib512Accessors {
    function from(uint512 r, uint256 x) internal pure returns (uint512 r_out) {
        assembly ("memory-safe") {
            mstore(r, 0x00)
            mstore(add(0x20, r), x)
            r_out := r
        }
    }

    function from(uint512 r, uint256 x_hi, uint256 x_lo) internal pure returns (uint512 r_out) {
        assembly ("memory-safe") {
            mstore(r, x_hi)
            mstore(add(0x20, r), x_lo)
            r_out := r
        }
    }

    function from(uint512 r, uint512 x) internal pure returns (uint512 r_out) {
        assembly ("memory-safe") {
            // Paradoxically, using `mload` and `mstore` here produces more
            // optimal code because it gives solc the opportunity to
            // optimize-out the use of memory entirely, in typical usage. As a
            // happy side effect, it also means that we don't have to deal with
            // Cancun hardfork compatibility issues
            mstore(r, mload(x))
            mstore(add(0x20, r), mload(add(0x20, x)))
            r_out := r
        }
    }

    function into(uint512 x) internal pure returns (uint256 r_hi, uint256 r_lo) {
        assembly ("memory-safe") {
            r_hi := mload(x)
            r_lo := mload(add(0x20, x))
        }
    }
}

using Lib512Accessors for uint512 global;

library Lib512Comparisons {
    function iszero(uint512 x) internal pure returns (bool r) {
        (uint256 x_hi, uint256 x_lo) = x.into();
        assembly ("memory-safe") {
            r := iszero(or(x_hi, x_lo))
        }
    }

    function eq(uint512 x, uint256 y) internal pure returns (bool r) {
        (uint256 x_hi, uint256 x_lo) = x.into();
        assembly ("memory-safe") {
            r := and(iszero(x_hi), eq(x_lo, y))
        }
    }

    function gt(uint512 x, uint256 y) internal pure returns (bool r) {
        (uint256 x_hi, uint256 x_lo) = x.into();
        assembly ("memory-safe") {
            r := or(gt(x_hi, 0x00), gt(x_lo, y))
        }
    }

    function lt(uint512 x, uint256 y) internal pure returns (bool r) {
        (uint256 x_hi, uint256 x_lo) = x.into();
        assembly ("memory-safe") {
            r := and(iszero(x_hi), lt(x_lo, y))
        }
    }

    function ne(uint512 x, uint256 y) internal pure returns (bool) {
        return !eq(x, y);
    }

    function ge(uint512 x, uint256 y) internal pure returns (bool) {
        return !lt(x, y);
    }

    function le(uint512 x, uint256 y) internal pure returns (bool) {
        return !gt(x, y);
    }

    function eq(uint512 x, uint512 y) internal pure returns (bool r) {
        (uint256 x_hi, uint256 x_lo) = x.into();
        (uint256 y_hi, uint256 y_lo) = y.into();
        assembly ("memory-safe") {
            r := and(eq(x_hi, y_hi), eq(x_lo, y_lo))
        }
    }

    function gt(uint512 x, uint512 y) internal pure returns (bool r) {
        (uint256 x_hi, uint256 x_lo) = x.into();
        (uint256 y_hi, uint256 y_lo) = y.into();
        assembly ("memory-safe") {
            r := or(gt(x_hi, y_hi), and(eq(x_hi, y_hi), gt(x_lo, y_lo)))
        }
    }

    function lt(uint512 x, uint512 y) internal pure returns (bool r) {
        (uint256 x_hi, uint256 x_lo) = x.into();
        (uint256 y_hi, uint256 y_lo) = y.into();
        assembly ("memory-safe") {
            r := or(lt(x_hi, y_hi), and(eq(x_hi, y_hi), lt(x_lo, y_lo)))
        }
    }

    function ne(uint512 x, uint512 y) internal pure returns (bool) {
        return !eq(x, y);
    }

    function ge(uint512 x, uint512 y) internal pure returns (bool) {
        return !lt(x, y);
    }

    function le(uint512 x, uint512 y) internal pure returns (bool) {
        return !gt(x, y);
    }
}

using Lib512Comparisons for uint512 global;

function __eq(uint512 x, uint512 y) pure returns (bool) {
    return x.eq(y);
}

function __gt(uint512 x, uint512 y) pure returns (bool) {
    return x.gt(y);
}

function __lt(uint512 x, uint512 y) pure returns (bool r) {
    return x.lt(y);
}

function __ne(uint512 x, uint512 y) pure returns (bool) {
    return x.ne(y);
}

function __ge(uint512 x, uint512 y) pure returns (bool) {
    return x.ge(y);
}

function __le(uint512 x, uint512 y) pure returns (bool) {
    return x.le(y);
}

using {__eq as ==, __gt as >, __lt as <, __ne as !=, __ge as >=, __le as <=} for uint512 global;

library Lib512Arithmetic {
    using UnsafeMath for uint256;

    function oadd(uint512 r, uint256 x, uint256 y) internal pure returns (uint512) {
        uint256 r_hi;
        uint256 r_lo;
        assembly ("memory-safe") {
            r_lo := add(x, y)
            // lt(r_lo, x) indicates overflow in the lower addition. We can add
            // the bool directly to the integer to perform carry
            r_hi := lt(r_lo, x)
        }
        return r.from(r_hi, r_lo);
    }

    function oadd(uint512 r, uint512 x, uint256 y) internal pure returns (uint512) {
        (uint256 x_hi, uint256 x_lo) = x.into();
        uint256 r_hi;
        uint256 r_lo;
        assembly ("memory-safe") {
            r_lo := add(x_lo, y)
            // lt(r_lo, x_lo) indicates overflow in the lower addition. Overflow
            // in the high limb is simply ignored
            r_hi := add(x_hi, lt(r_lo, x_lo))
        }
        return r.from(r_hi, r_lo);
    }

    function iadd(uint512 r, uint256 y) internal pure returns (uint512) {
        return oadd(r, r, y);
    }

    function oadd(uint512 r, uint512 x, uint512 y) internal pure returns (uint512) {
        (uint256 x_hi, uint256 x_lo) = x.into();
        (uint256 y_hi, uint256 y_lo) = y.into();
        uint256 r_hi;
        uint256 r_lo;
        assembly ("memory-safe") {
            r_lo := add(x_lo, y_lo)
            // lt(r_lo, x_lo) indicates overflow in the lower addition. Overflow
            // in the high limb is simply ignored
            r_hi := add(add(x_hi, y_hi), lt(r_lo, x_lo))
        }
        return r.from(r_hi, r_lo);
    }

    function iadd(uint512 r, uint512 y) internal pure returns (uint512) {
        return oadd(r, r, y);
    }

    function osub(uint512 r, uint512 x, uint256 y) internal pure returns (uint512) {
        (uint256 x_hi, uint256 x_lo) = x.into();
        uint256 r_hi;
        uint256 r_lo;
        assembly ("memory-safe") {
            // gt(y, x_lo) indicates underflow in the lower subtraction. We can
            // subtract the bool directly from the integer to perform carry
            r_lo := sub(x_lo, y)
            r_hi := sub(x_hi, gt(y, x_lo))
        }
        return r.from(r_hi, r_lo);
    }

    function isub(uint512 r, uint256 y) internal pure returns (uint512) {
        return osub(r, r, y);
    }

    function _sub(uint256 x_hi, uint256 x_lo, uint256 y_hi, uint256 y_lo)
        private
        pure
        returns (uint256 r_hi, uint256 r_lo)
    {
        assembly ("memory-safe") {
            // gt(y_lo, x_lo) indicates underflow in the lower subtraction.
            // Underflow in the high limb is simply ignored
            r_lo := sub(x_lo, y_lo)
            r_hi := sub(sub(x_hi, y_hi), gt(y_lo, x_lo))
        }
    }

    function osub(uint512 r, uint512 x, uint512 y) internal pure returns (uint512) {
        (uint256 x_hi, uint256 x_lo) = x.into();
        (uint256 y_hi, uint256 y_lo) = y.into();
        (uint256 r_hi, uint256 r_lo) = _sub(x_hi, x_lo, y_hi, y_lo);
        return r.from(r_hi, r_lo);
    }

    function isub(uint512 r, uint512 y) internal pure returns (uint512) {
        return osub(r, r, y);
    }

    //// The technique implemented in the following functions for multiplication is
    //// adapted from Remco Bloemen's work https://2π.com/17/full-mul/ .
    //// The original code was released under the MIT license.

    function _mul(uint256 x, uint256 y) private pure returns (uint256 r_hi, uint256 r_lo) {
        assembly ("memory-safe") {
            let mm := mulmod(x, y, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
            r_lo := mul(x, y)
            r_hi := sub(sub(mm, r_lo), lt(mm, r_lo))
        }
    }

    function _mul(uint256 x_hi, uint256 x_lo, uint256 y) private pure returns (uint256 r_hi, uint256 r_lo) {
        assembly ("memory-safe") {
            let mm := mulmod(x_lo, y, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
            r_lo := mul(x_lo, y)
            r_hi := add(mul(x_hi, y), sub(sub(mm, r_lo), lt(mm, r_lo)))
        }
    }

    function _mul(uint256 x_hi, uint256 x_lo, uint256 y_hi, uint256 y_lo)
        private
        pure
        returns (uint256 r_hi, uint256 r_lo)
    {
        assembly ("memory-safe") {
            let mm := mulmod(x_lo, y_lo, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
            r_lo := mul(x_lo, y_lo)
            r_hi := add(sub(sub(mm, r_lo), lt(mm, r_lo)), add(mul(x_hi, y_lo), mul(x_lo, y_hi)))
        }
    }

    function omul(uint512 r, uint256 x, uint256 y) internal pure returns (uint512) {
        (uint256 r_hi, uint256 r_lo) = _mul(x, y);
        return r.from(r_hi, r_lo);
    }

    function omul(uint512 r, uint512 x, uint256 y) internal pure returns (uint512) {
        (uint256 x_hi, uint256 x_lo) = x.into();
        (uint256 r_hi, uint256 r_lo) = _mul(x_hi, x_lo, y);
        return r.from(r_hi, r_lo);
    }

    function imul(uint512 r, uint256 y) internal pure returns (uint512) {
        return omul(r, r, y);
    }

    function omul(uint512 r, uint512 x, uint512 y) internal pure returns (uint512) {
        (uint256 x_hi, uint256 x_lo) = x.into();
        (uint256 y_hi, uint256 y_lo) = y.into();
        (uint256 r_hi, uint256 r_lo) = _mul(x_hi, x_lo, y_hi, y_lo);
        return r.from(r_hi, r_lo);
    }

    function imul(uint512 r, uint512 y) internal pure returns (uint512) {
        return omul(r, r, y);
    }

    function mod(uint512 n, uint256 d) internal pure returns (uint256 r) {
        (uint256 n_hi, uint256 n_lo) = n.into();
        assembly ("memory-safe") {
            r := mulmod(n_hi, sub(0x00, d), d)
            r := addmod(n_lo, r, d)
        }
    }

    function omod(uint512 r, uint512 x, uint512 y) internal view returns (uint512) {
        (uint256 x_hi, uint256 x_lo) = x.into();
        (uint256 y_hi, uint256 y_lo) = y.into();
        assembly ("memory-safe") {
            // We use the MODEXP (5) precompile with an exponent of 1. We encode
            // the arguments to the precompile at the beginning of free memory
            // without allocating. Arguments are encoded as:
            //     [64 32 64 x_hi x_lo 1 y_hi y_lo]
            let ptr := mload(0x40)
            mstore(ptr, 0x40)
            mstore(add(0x20, ptr), 0x20)
            mstore(add(0x40, ptr), 0x40)
            // See comment in `from` about why `mstore` is more efficient than `mcopy`
            mstore(add(0x60, ptr), x_hi)
            mstore(add(0x80, ptr), x_lo)
            mstore(add(0xa0, ptr), 0x01)
            mstore(add(0xc0, ptr), y_hi)
            mstore(add(0xe0, ptr), y_lo)

            // We write the result of MODEXP directly into the output space r.
            pop(staticcall(gas(), 0x05, ptr, 0x100, r, 0x40))
            // The MODEXP precompile can only fail due to out-of-gas. This call
            // consumes only 200 gas, so if it failed, there is only 4 gas
            // remaining in this context. Therefore, we will out-of-gas
            // immediately when we attempt to read the result. We don't bother
            // to check for failure.
        }
        return r;
    }

    function imod(uint512 r, uint512 y) internal view returns (uint512) {
        return omod(r, r, y);
    }

    //// The technique implemented in the following functions for division is
    //// adapted from Remco Bloemen's work https://2π.com/21/muldiv/ .
    //// The original code was released under the MIT license.

    function _roundDown(uint256 x_hi, uint256 x_lo, uint256 d) private pure returns (uint256 r_hi, uint256 r_lo) {
        assembly ("memory-safe") {
            // Get the remainder [n_hi n_lo] % d (< 2²⁵⁶)
            // 2**256 % d = -d % 2**256 % d -- https://2π.com/17/512-bit-division/
            let rem := mulmod(x_hi, sub(0x00, d), d)
            rem := addmod(x_lo, rem, d)

            r_hi := sub(x_hi, gt(rem, x_lo))
            r_lo := sub(x_lo, rem)
        }
    }

    function _roundDown(uint256 x_hi, uint256 x_lo, uint256 d_hi, uint256 d_lo)
        private
        view
        returns (uint256 r_hi, uint256 r_lo)
    {
        uint512 r;
        assembly ("memory-safe") {
            // We point r to the beginning of free memory WITHOUT allocating.
            // This is not technically "memory-safe" because solc might use that
            // memory for something in between the end of this assembly block
            // and the beginning of the call to into(), but empirically and
            // practically speaking that won't and doesn't happen. We save some
            // gas by not bumping the free pointer.
            r := mload(0x40)

            // Get the remainder [x_hi x_lo] % [d_hi d_lo] (< 2⁵¹²) We use the
            // MODEXP (5) precompile with an exponent of 1. We encode the
            // arguments to the precompile at the beginning of free memory
            // without allocating. Conveniently, r already points to this
            // region. Arguments are encoded as. Arguments are encoded as:
            //     [64 32 64 x_hi x_lo 1 d_hi d_lo]
            mstore(r, 0x40)
            mstore(add(0x20, r), 0x20)
            mstore(add(0x40, r), 0x40)
            mstore(add(0x60, r), x_hi)
            mstore(add(0x80, r), x_lo)
            mstore(add(0xa0, r), 0x01)
            mstore(add(0xc0, r), d_hi)
            mstore(add(0xe0, r), d_lo)

            // The MODEXP precompile can only fail due to out-of-gas. This call
            // consumes only 200 gas, so if it failed, there is only 4 gas
            // remaining in this context. Therefore, we will out-of-gas
            // immediately when we attempt to read the result. We don't bother
            // to check for failure.
            pop(staticcall(gas(), 0x05, r, 0x100, r, 0x40))
        }
        (uint256 rem_hi, uint256 rem_lo) = r.into();
        // Round down by subtracting the remainder from the numerator
        (r_hi, r_lo) = _sub(x_hi, x_lo, rem_hi, rem_lo);
    }

    function _twos(uint256 x) private pure returns (uint256 twos, uint256 twosInv) {
        assembly ("memory-safe") {
            // Compute largest power of two divisor of x. x is nonzero, so this
            // is always ≥ 1.
            twos := and(sub(0x00, x), x)

            // To shift up (bits from the high limb into the low limb) we need
            // the inverse of `twos`. That is, 2²⁵⁶ / twos.
            //     2**256 / twos = -twos % 2**256 / twos + 1 -- https://2π.com/17/512-bit-division/
            // If twos is zero, then twosInv becomes one (not possible)
            twosInv := add(div(sub(0x00, twos), twos), 0x01)
        }
    }

    function _toOdd256(uint256 x_hi, uint256 x_lo, uint256 y) private pure returns (uint256 x_lo_out, uint256 y_out) {
        // Factor powers of two out of y and apply the same shift to [x_hi x_lo]
        (uint256 twos, uint256 twosInv) = _twos(y);

        assembly ("memory-safe") {
            // Divide y by the power of two
            y_out := div(y, twos)

            // Divide [x_hi x_lo] by the power of two
            x_lo_out := or(div(x_lo, twos), mul(x_hi, twosInv))
        }
    }

    function _toOdd256(uint256 x_hi, uint256 x_lo, uint256 y_hi, uint256 y_lo)
        private
        pure
        returns (uint256 x_lo_out, uint256 y_lo_out)
    {
        // Factor powers of two out of y_lo and apply the same shift to x_lo
        (uint256 twos, uint256 twosInv) = _twos(y_lo);

        assembly ("memory-safe") {
            // Divide [y_hi y_lo] by the power of two, returning only the low limb
            y_lo_out := or(div(y_lo, twos), mul(y_hi, twosInv))

            // Divide [x_hi x_lo] by the power of two, returning only the low limb
            x_lo_out := or(div(x_lo, twos), mul(x_hi, twosInv))
        }
    }

    function _toOdd512(uint256 x_hi, uint256 x_lo, uint256 y)
        private
        pure
        returns (uint256 x_hi_out, uint256 x_lo_out, uint256 y_out)
    {
        // Factor powers of two out of y and apply the same shift to [x_hi x_lo]
        (uint256 twos, uint256 twosInv) = _twos(y);

        assembly ("memory-safe") {
            // Divide y by the power of two
            y_out := div(y, twos)

            // Divide [x_hi x_lo] by the power of two
            x_hi_out := div(x_hi, twos)
            x_lo_out := or(div(x_lo, twos), mul(x_hi, twosInv))
        }
    }

    function _toOdd512(uint256 x_hi, uint256 x_lo, uint256 y_hi, uint256 y_lo)
        private
        pure
        returns (uint256 x_hi_out, uint256 x_lo_out, uint256 y_hi_out, uint256 y_lo_out)
    {
        // Factor powers of two out of [y_hi y_lo] and apply the same shift to
        // [x_hi x_lo] and [y_hi y_lo]
        (uint256 twos, uint256 twosInv) = _twos(y_lo);

        assembly ("memory-safe") {
            // Divide [y_hi y_lo] by the power of two
            y_hi_out := div(y_hi, twos)
            y_lo_out := or(div(y_lo, twos), mul(y_hi, twosInv))

            // Divide [x_hi x_lo] by the power of two
            x_hi_out := div(x_hi, twos)
            x_lo_out := or(div(x_lo, twos), mul(x_hi, twosInv))
        }
    }

    function _invert256(uint256 d) private pure returns (uint256 inv) {
        assembly ("memory-safe") {
            // Invert d mod 2²⁵⁶ -- https://2π.com/18/multiplitcative-inverses/
            // d is an odd number (from _toOdd*). It has an inverse modulo 2²⁵⁶
            // such that d * inv ≡ 1 mod 2²⁵⁶.
            // We use Newton-Raphson iterations compute inv. Thanks to Hensel's
            // lifting lemma, this also works in modular arithmetic, doubling
            // the correct bits in each step. The Newton-Raphson-Hensel step is:
            //    inv_{n+1} = inv_n * (2 - d*inv_n) % 2**512

            // To kick off Newton-Raphson-Hensel iterations, we start with a
            // seed of the inverse that is correct correct for four bits.
            //     d * inv ≡ 1 mod 2⁴
            inv := xor(mul(0x03, d), 0x02)

            // Each Newton-Raphson-Hensel step doubles the number of correct
            // bits in inv. After 6 iterations, full convergence is guaranteed.
            inv := mul(inv, sub(0x02, mul(d, inv))) // inverse mod 2⁸
            inv := mul(inv, sub(0x02, mul(d, inv))) // inverse mod 2¹⁶
            inv := mul(inv, sub(0x02, mul(d, inv))) // inverse mod 2³²
            inv := mul(inv, sub(0x02, mul(d, inv))) // inverse mod 2⁶⁴
            inv := mul(inv, sub(0x02, mul(d, inv))) // inverse mod 2¹²⁸
            inv := mul(inv, sub(0x02, mul(d, inv))) // inverse mod 2²⁵⁶
        }
    }

    function _invert512(uint256 d) private pure returns (uint256 inv_hi, uint256 inv_lo) {
        // First, we get the inverse of d mod 2²⁵⁶
        inv_lo = _invert256(d);

        // To extend this to the inverse mod 2⁵¹², we perform a more elaborate
        // 7th Newton-Raphson-Hensel iteration with 512 bits of precision.

        // tmp = d * inv_lo % 2**512
        (uint256 tmp_hi, uint256 tmp_lo) = _mul(d, inv_lo);

        assembly ("memory-safe") {
            // tmp = 2 - tmp % 2**512
            tmp_hi := sub(sub(0x00, tmp_hi), gt(tmp_lo, 0x02))
            tmp_lo := sub(0x02, tmp_lo)

            // inv_hi = inv_lo * tmp / 2**256 % 2**256
            let mm := mulmod(inv_lo, tmp_lo, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
            inv_hi := add(sub(sub(mm, inv_lo), lt(mm, inv_lo)), mul(inv_lo, tmp_hi))
        }
    }

    function _invert512(uint256 d_hi, uint256 d_lo) private pure returns (uint256 inv_hi, uint256 inv_lo) {
        // First, we get the inverse of d mod 2²⁵⁶
        inv_lo = _invert256(d_lo);

        // To extend this to the inverse mod 2⁵¹², we perform a more elaborate
        // 7th Newton-Raphson-Hensel iteration with 512 bits of precision.

        // tmp = d * inv_lo % 2**512
        (uint256 tmp_hi, uint256 tmp_lo) = _mul(d_hi, d_lo, inv_lo);

        assembly ("memory-safe") {
            // tmp = 2 - tmp % 2**512
            tmp_hi := sub(sub(0x00, tmp_hi), gt(tmp_lo, 0x02))
            tmp_lo := sub(0x02, tmp_lo)

            // inv_hi = inv_lo * tmp / 2**256 % 2**256
            let mm := mulmod(inv_lo, tmp_lo, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
            inv_hi := add(sub(sub(mm, inv_lo), lt(mm, inv_lo)), mul(inv_lo, tmp_hi))
        }
    }

    function div(uint512 n, uint256 d) internal pure returns (uint256) {
        if (d == 0) {
            Panic.panic(Panic.DIVISION_BY_ZERO);
        }

        (uint256 n_hi, uint256 n_lo) = n.into();
        if (n_hi == 0) {
            return n_lo.unsafeDiv(d);
        }

        // Round the numerator down to a multiple of the denominator. This makes
        // the division exact without affecting the result.
        (n_hi, n_lo) = _roundDown(n_hi, n_lo, d);

        // Make d odd so that it has a multiplicative inverse mod 2²⁵⁶
        // After this we can discard n_hi because our result is only 256 bits
        (n_lo, d) = _toOdd256(n_hi, n_lo, d);

        // We perform division by multiplying by the multiplicative inverse of
        // the denominator mod 2²⁵⁶. Since d is odd, this inverse
        // exists. Compute that inverse
        d = _invert256(d);

        unchecked {
            // Because the division is now exact (we rounded n down to a
            // multiple of d), we perform it by multiplying with the modular
            // inverse of the denominator. This is the correct result mod 2²⁵⁶.
            return n_lo * d;
        }
    }

    function div(uint512 n, uint512 d) internal view returns (uint256) {
        (uint256 d_hi, uint256 d_lo) = d.into();
        if (d_hi == 0) {
            return div(n, d_lo);
        }

        uint256 n_hi;
        assembly ("memory-safe") {
            n_hi := mload(n)
        }
        if (d_lo == 0) {
            return n_hi.unsafeDiv(d_hi);
        }
        if (n_hi == 0) {
            // TODO: this optimization may not be overall optimizing
            return 0;
        }
        uint256 n_lo;
        assembly ("memory-safe") {
            n_lo := mload(add(0x20, n))
        }

        // Round the numerator down to a multiple of the denominator. This makes
        // the division exact without affecting the result.
        (n_hi, n_lo) = _roundDown(n_hi, n_lo, d_hi, d_lo);

        // Make d_lo odd so that it has a multiplicative inverse mod 2²⁵⁶
        // After this we can discard n_hi and d_hi because our result is only
        // 256 bits
        (n_lo, d_lo) = _toOdd256(n_hi, n_lo, d_hi, d_lo);

        // We perform division by multiplying by the multiplicative inverse of
        // the denominator mod 2²⁵⁶. Since d is odd, this inverse
        // exists. Compute that inverse
        d_lo = _invert256(d_lo);

        unchecked {
            // Because the division is now exact (we rounded n down to a
            // multiple of d), we perform it by multiplying with the modular
            // inverse of the denominator. This is the correct result mod 2²⁵⁶.
            return n_lo * d_lo;
        }
    }

    function odiv(uint512 r, uint512 x, uint256 y) internal pure returns (uint512) {
        if (y == 0) {
            Panic.panic(Panic.DIVISION_BY_ZERO);
        }

        (uint256 x_hi, uint256 x_lo) = x.into();
        if (x_hi == 0) {
            return r.from(0, x_lo.unsafeDiv(y));
        }

        // Round the numerator down to a multiple of the denominator. This makes
        // the division exact without affecting the result.
        (x_hi, x_lo) = _roundDown(x_hi, x_lo, y);

        // Make y odd so that it has a multiplicative inverse mod 2⁵¹²
        (x_hi, x_lo, y) = _toOdd512(x_hi, x_lo, y);

        // We perform division by multiplying by the multiplicative inverse of
        // the denominator mod 2⁵¹². Since y is odd, this inverse
        // exists. Compute that inverse
        (uint256 inv_hi, uint256 inv_lo) = _invert512(y);

        // Because the division is now exact (we rounded x down to a multiple of
        // y), we perform it by multiplying with the modular inverse of the
        // denominator.
        (uint256 r_hi, uint256 r_lo) = _mul(x_hi, x_lo, inv_hi, inv_lo);
        return r.from(r_hi, r_lo);
    }

    function idiv(uint512 r, uint256 y) internal pure returns (uint512) {
        return odiv(r, r, y);
    }

    function odiv(uint512 r, uint512 x, uint512 y) internal view returns (uint512) {
        (uint256 y_hi, uint256 y_lo) = y.into();
        if (y_hi == 0) {
            return odiv(r, x, y_lo);
        }

        uint256 x_hi;
        assembly ("memory-safe") {
            x_hi := mload(x)
        }
        if (y_lo == 0) {
            return r.from(0, x_hi.unsafeDiv(y_hi));
        }
        if (x_hi == 0) {
            // TODO: this optimization may not be overall optimizing
            return r.from(0, 0);
        }
        uint256 x_lo;
        assembly ("memory-safe") {
            x_lo := mload(add(0x20, x))
        }

        // Round the numerator down to a multiple of the denominator. This makes
        // the division exact without affecting the result.
        (x_hi, x_lo) = _roundDown(x_hi, x_lo, y_hi, y_lo);

        // Make y odd so that it has a multiplicative inverse mod 2⁵¹²
        (x_hi, x_lo, y_hi, y_lo) = _toOdd512(x_hi, x_lo, y_hi, y_lo);

        // We perform division by multiplying by the multiplicative inverse of
        // the denominator mod 2⁵¹². Since y is odd, this inverse
        // exists. Compute that inverse
        (y_hi, y_lo) = _invert512(y_hi, y_lo);

        // Because the division is now exact (we rounded x down to a multiple of
        // y), we perform it by multiplying with the modular inverse of the
        // denominator.
        (uint256 r_hi, uint256 r_lo) = _mul(x_hi, x_lo, y_hi, y_lo);
        return r.from(r_hi, r_lo);
    }

    function idiv(uint512 r, uint512 y) internal view returns (uint512) {
        return odiv(r, r, y);
    }
}

using Lib512Arithmetic for uint512 global;

library Lib512UserDefinedHelpers {
    function checkNull(uint512 x, uint512 y) internal pure {
        assembly ("memory-safe") {
            if iszero(mul(x, y)) {
                mstore(0x00, 0x4e487b71) // selector for `Panic(uint256)`
                mstore(0x20, 0x01) // code for "assertion failure"
            }
        }
    }

    function smuggleToPure(function (uint512, uint512, uint512) internal view returns (uint512) f)
        internal
        pure
        returns (function (uint512, uint512, uint512) internal pure returns (uint512) r)
    {
        assembly ("memory-safe") {
            r := f
        }
    }

    function omod(uint512 r, uint512 x, uint512 y) internal view returns (uint512) {
        return r.omod(x, y);
    }

    function odiv(uint512 r, uint512 x, uint512 y) internal view returns (uint512) {
        return r.odiv(x, y);
    }
}

function __add(uint512 x, uint512 y) pure returns (uint512 r) {
    Lib512UserDefinedHelpers.checkNull(x, y);
    r.oadd(x, y);
}

function __sub(uint512 x, uint512 y) pure returns (uint512 r) {
    Lib512UserDefinedHelpers.checkNull(x, y);
    r.osub(x, y);
}

function __mul(uint512 x, uint512 y) pure returns (uint512 r) {
    Lib512UserDefinedHelpers.checkNull(x, y);
    r.omul(x, y);
}

function __mod(uint512 x, uint512 y) pure returns (uint512 r) {
    Lib512UserDefinedHelpers.checkNull(x, y);
    Lib512UserDefinedHelpers.smuggleToPure(Lib512UserDefinedHelpers.omod)(r, x, y);
}

function __div(uint512 x, uint512 y) pure returns (uint512 r) {
    Lib512UserDefinedHelpers.checkNull(x, y);
    Lib512UserDefinedHelpers.smuggleToPure(Lib512UserDefinedHelpers.odiv)(r, x, y);
}

using {__add as +, __sub as -, __mul as *, __mod as %, __div as / } for uint512 global;

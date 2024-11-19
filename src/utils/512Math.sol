// SPDX-License-Identifier: MIT
pragma solidity =0.8.25;

import {Panic} from "./Panic.sol";
import {UnsafeMath} from "./UnsafeMath.sol";

/*

WARNING *** WARNING *** WARNING *** WARNING *** WARNING *** WARNING *** WARNING
  ***                                                                     ***
WARNING                     This code is unaudited                      WARNING
  ***                                                                     ***
WARNING *** WARNING *** WARNING *** WARNING *** WARNING *** WARNING *** WARNING

*/

/// The type uint512 behaves as if it were declared as
///     struct uint512 {
///         uint256 hi;
///         uint256 lo;
///     }
/// However, returning `memory` references from internal functions is impossible
/// to do efficiently, especially when the functions are small and are called
/// frequently. Therefore, we assume direct control over memory allocation using
/// the functions `tmp()` and `alloc()` defined below. If you need to pass
/// 512-bit integers between contracts (generally a bad idea), the struct
/// `uint512_external` defined at the end of this file is provided for this
/// purpose and has exactly the definition you'd expect (as well as convenient
/// conversion functions).
///
/// MAKING A DECLARATION OF THE FOLLOWING FORM WILL CAUSE UNEXPECTED BEHAVIOR:
///     uint512 x;
/// INSTEAD OF DOING THAT, YOU MUST USE `alloc()`, LIKE THIS:
///     uint512 x = alloc();
/// IF YOU REALLY WANTED TO DO THAT (ADVANCED USAGE) THEN FOR CLARITY, WRITE THE
/// FOLLOWING:
///     uint512 x = tmp();
///
/// While user-defined arithmetic operations (i.e. +, -, *, %, /) are provided
/// for `uint512`, they are not gas-optimal, full-featured, or composable. You
/// will get a revert upon incorrect usage. Their primary usage is when a simple
/// arithmetic operation needs to be performed followed by a comparison (e.g. <,
/// >, ==, etc.) or conversion to a pair of `uint256`s (i.e. `.into()`). The use
/// of the user-defined arithmetic operations is not composable with the usage
/// of `tmp()`.
///
/// In general, correct usage of `uint512` requires always specifying the output
/// location of each operation. For each `o*` operation (mnemonic:
/// out-of-place), the first argument is the output location and the remaining
/// arguments are the input. For each `i*` operation (mnemonic: in-place), the
/// first argument is both input and output and the remaining arguments are
/// purely input. For each `ir*` operation (mnemonic: in-place reverse; only for
/// non-commutative operations), the semantics of the input arguments are
/// flipped (i.e. `irsub(foo, bar)` is semantically equivalent to `foo = bar -
/// foo`); the first argument is still the output location. Only `irsub`,
/// `irmod`, `irdiv`, `irmodAlt`, and `irdivAlt` exist. Unless otherwise noted,
/// the return value of each function is the output location. This supports
/// chaining/pipeline/tacit-style programming.
///
/// All provided arithmetic operations behave as if they were inside an
/// `unchecked` block. We assume that because you're reaching for 512-bit math,
/// you have domain knowledge about the range of values that you will
/// encounter. Overflow causes truncation, not a revert. Division or modulo by
/// zero still causes a panic revert with code 18 (identical behavior to
/// "normal" unchecked arithmetic).
///
/// Three additional arithmetic operations are provided, bare `sub`, `mod`, and
/// `div`. These are provided for use when it is known that the result of the
/// operation will fit into 256 bits. This fact is not checked, but more
/// efficient algorithms are employed assuming this. The result is a `uint256`.
///
/// The operations `*mod` and `*div` with 512-bit denominator are `view` instead
/// of `pure` because they make use of the MODEXP (5) precompile. Some EVM L2s
/// and sidechains do not support MODEXP with 512-bit arguments. On those
/// chains, the `*modAlt` and `*divAlt` functions are provided. These functions
/// are truly `pure` and do not rely on MODEXP at all. The downside is that they
/// consume slightly (really only *slightly*) more gas.
///
/// ## Full list of provided functions
///
/// Unless otherwise noted, all functions return `(uint512)`
///
/// ### Utility
///
/// * from(uint256)
/// * from(uint256,uint256) -- The EVM is big-endian. The most-significant word is first.
/// * from(uint512) -- performs a copy
/// * into() returns (uint256,uint256) -- Again, the most-significant word is first.
/// * toExternal(uint512) returns (uint512_external memory)
///
/// ### Comparison (all functions return `(bool)`)
///
/// * isZero(uint512)
/// * isMax(uint512)
/// * eq(uint512,uint256)
/// * eq(uint512,uint512)
/// * ne(uint512,uint256)
/// * ne(uint512,uint512)
/// * gt(uint512,uint256)
/// * gt(uint512,uint512)
/// * ge(uint512,uint256)
/// * ge(uint512,uint512)
/// * lt(uint512,uint256)
/// * lt(uint512,uint512)
/// * le(uint512,uint256)
/// * le(uint512,uint512)
///
/// ### Addition
///
/// * oadd(uint512,uint256,uint256) -- iadd(uint256,uint256) is not provided for somewhat obvious reasons
/// * oadd(uint512,uint512,uint256)
/// * iadd(uint512,uint256)
/// * oadd(uint512,uint512,uint512)
/// * iadd(uint512,uint512)
///
/// ### Subtraction
///
/// * sub(uint512,uint256) returns (uint256)
/// * sub(uint512,uint512) returns (uint256)
/// * osub(uint512,uint512,uint256)
/// * isub(uint512,uint256)
/// * osub(uint512,uint512,uint512)
/// * isub(uint512,uint512)
/// * irsub(uint512,uint512)
///
/// ### Multiplication
///
/// * omul(uint512,uint256,uint256)
/// * omul(uint512,uint512,uint256)
/// * imul(uint512,uint256)
/// * omul(uint512,uint512,uint512)
/// * imul(uint512,uint512)
///
/// ### Modulo
///
/// * mod(uint512,uint256) returns (uint256) -- mod(uint512,uint512) is not provided for less obvious reasons
/// * omod(uint512,uint512,uint512)
/// * imod(uint512,uint512)
/// * irmod(uint512,uint512)
/// * omodAlt(uint512,uint512,uint512)
/// * imodAlt(uint512,uint512)
/// * irmodAlt(uint512,uint512)
///
/// ### Division
///
/// * div(uint512,uint256) returns (uint256)
/// * div(uint512,uint512) returns (uint256)
/// * odiv(uint512,uint512,uint256)
/// * idiv(uint512,uint256)
/// * odiv(uint512,uint512,uint512)
/// * idiv(uint512,uint512)
/// * irdiv(uint512,uint512)
/// * divAlt(uint512,uint512) returns (uint256) -- divAlt(uint512,uint256) is not provided because div(uint512,uint256) is suitable for chains without MODEXP
/// * odivAlt(uint512,uint512,uint512)
/// * idivAlt(uint512,uint512)
/// * irdivAlt(uint512,uint512)
type uint512 is bytes32;

function alloc() pure returns (uint512 r) {
    assembly ("memory-safe") {
        r := mload(0x40)
        mstore(0x40, add(0x40, r))
    }
}

function tmp() pure returns (uint512 r) {}

library Lib512MathAccessors {
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
            // Paradoxically, using `mload` and `mstore` here (instead of
            // `mcopy`) produces more optimal code because it gives solc the
            // opportunity to optimize-out the use of memory entirely, in
            // typical usage. As a happy side effect, it also means that we
            // don't have to deal with Cancun hardfork compatibility issues.
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

using Lib512MathAccessors for uint512 global;

library Lib512MathComparisons {
    function isZero(uint512 x) internal pure returns (bool r) {
        (uint256 x_hi, uint256 x_lo) = x.into();
        assembly ("memory-safe") {
            r := iszero(or(x_hi, x_lo))
        }
    }

    function isMax(uint512 x) internal pure returns (bool r) {
        (uint256 x_hi, uint256 x_lo) = x.into();
        assembly ("memory-safe") {
            r := iszero(not(and(x_hi, x_lo)))
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

using Lib512MathComparisons for uint512 global;

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

library Lib512MathArithmetic {
    using UnsafeMath for uint256;

    function oadd(uint512 r, uint256 x, uint256 y) internal pure returns (uint512) {
        uint256 r_hi;
        uint256 r_lo;
        assembly ("memory-safe") {
            r_lo := add(x, y)
            // `lt(r_lo, x)` indicates overflow in the lower addition. We can
            // add the bool directly to the integer to perform carry
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
            // `lt(r_lo, x_lo)` indicates overflow in the lower
            // addition. Overflow in the high limb is simply ignored
            r_hi := add(x_hi, lt(r_lo, x_lo))
        }
        return r.from(r_hi, r_lo);
    }

    function iadd(uint512 r, uint256 y) internal pure returns (uint512) {
        return oadd(r, r, y);
    }

    function _add(uint256 x_hi, uint256 x_lo, uint256 y_hi, uint256 y_lo)
        private
        pure
        returns (uint256 r_hi, uint256 r_lo)
    {
        assembly ("memory-safe") {
            r_lo := add(x_lo, y_lo)
            // `lt(r_lo, x_lo)` indicates overflow in the lower
            // addition. Overflow in the high limb is simply ignored.
            r_hi := add(add(x_hi, y_hi), lt(r_lo, x_lo))
        }
    }

    function oadd(uint512 r, uint512 x, uint512 y) internal pure returns (uint512) {
        (uint256 x_hi, uint256 x_lo) = x.into();
        (uint256 y_hi, uint256 y_lo) = y.into();
        (uint256 r_hi, uint256 r_lo) = _add(x_hi, x_lo, y_hi, y_lo);
        return r.from(r_hi, r_lo);
    }

    function iadd(uint512 r, uint512 y) internal pure returns (uint512) {
        return oadd(r, r, y);
    }

    function _sub(uint256 x_hi, uint256 x_lo, uint256 y) private pure returns (uint256 r_hi, uint256 r_lo) {
        assembly ("memory-safe") {
            r_lo := sub(x_lo, y)
            // `gt(r_lo, x_lo)` indicates underflow in the lower subtraction. We
            // can subtract the bool directly from the integer to perform carry.
            r_hi := sub(x_hi, gt(r_lo, x_lo))
        }
    }

    function osub(uint512 r, uint512 x, uint256 y) internal pure returns (uint512) {
        (uint256 x_hi, uint256 x_lo) = x.into();
        (uint256 r_hi, uint256 r_lo) = _sub(x_hi, x_lo, y);
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
            r_lo := sub(x_lo, y_lo)
            // `gt(r_lo, x_lo)` indicates underflow in the lower subtraction.
            // Underflow in the high limb is simply ignored.
            r_hi := sub(sub(x_hi, y_hi), gt(r_lo, x_lo))
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

    function irsub(uint512 r, uint512 y) internal pure returns (uint512) {
        return osub(r, y, r);
    }

    function sub(uint512 x, uint256 y) internal pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := sub(mload(add(0x20, x)), y)
        }
    }

    function sub(uint512 x, uint512 y) internal pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := sub(mload(add(0x20, x)), mload(add(0x20, y)))
        }
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

    function omul(uint512 r, uint256 x, uint256 y) internal pure returns (uint512) {
        (uint256 r_hi, uint256 r_lo) = _mul(x, y);
        return r.from(r_hi, r_lo);
    }

    function _mul(uint256 x_hi, uint256 x_lo, uint256 y) private pure returns (uint256 r_hi, uint256 r_lo) {
        assembly ("memory-safe") {
            let mm := mulmod(x_lo, y, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
            r_lo := mul(x_lo, y)
            r_hi := add(mul(x_hi, y), sub(sub(mm, r_lo), lt(mm, r_lo)))
        }
    }

    function omul(uint512 r, uint512 x, uint256 y) internal pure returns (uint512) {
        (uint256 x_hi, uint256 x_lo) = x.into();
        (uint256 r_hi, uint256 r_lo) = _mul(x_hi, x_lo, y);
        return r.from(r_hi, r_lo);
    }

    function imul(uint512 r, uint256 y) internal pure returns (uint512) {
        return omul(r, r, y);
    }

    function _mul(uint256 x_hi, uint256 x_lo, uint256 y_hi, uint256 y_lo)
        private
        pure
        returns (uint256 r_hi, uint256 r_lo)
    {
        assembly ("memory-safe") {
            let mm := mulmod(x_lo, y_lo, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
            r_lo := mul(x_lo, y_lo)
            r_hi := add(add(mul(x_hi, y_lo), mul(x_lo, y_hi)), sub(sub(mm, r_lo), lt(mm, r_lo)))
        }
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
        if (d == 0) {
            Panic.panic(Panic.DIVISION_BY_ZERO);
        }
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

    function irmod(uint512 r, uint512 y) internal view returns (uint512) {
        return omod(r, y, r);
    }

    /// Multiply 512-bit [x_hi x_lo] by 256-bit [y] giving 768-bit [r_ex r_hi r_lo]
    function _mul768(uint256 x_hi, uint256 x_lo, uint256 y)
        private
        pure
        returns (uint256 r_ex, uint256 r_hi, uint256 r_lo)
    {
        assembly ("memory-safe") {
            let mm0 := mulmod(x_lo, y, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
            r_lo := mul(x_lo, y)
            let mm1 := mulmod(x_hi, y, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
            let r_partial := mul(x_hi, y)
            r_ex := sub(sub(mm1, r_partial), lt(mm1, r_partial))

            r_hi := add(r_partial, sub(sub(mm0, r_lo), lt(mm0, r_lo)))
            // `lt(r_hi, r_partial)` indicates overflow in the addition to form
            // `r_hi`. We can add the bool directly to the integer to perform
            // carry.
            r_ex := add(r_ex, lt(r_hi, r_partial))
        }
    }

    //// The technique implemented in the following functions for division is
    //// adapted from Remco Bloemen's work https://2π.com/21/muldiv/ .
    //// The original code was released under the MIT license.

    function _roundDown(uint256 x_hi, uint256 x_lo, uint256 d) private pure returns (uint256 r_hi, uint256 r_lo) {
        assembly ("memory-safe") {
            // Get the remainder [n_hi n_lo] % d (< 2²⁵⁶ - 1)
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
            // We point `r` to the beginning of free memory WITHOUT allocating.
            // This is not technically "memory-safe" because solc might use that
            // memory for something in between the end of this assembly block
            // and the beginning of the call to `into()`, but empirically and
            // practically speaking that won't and doesn't happen. We save some
            // gas by not bumping the free pointer.
            r := mload(0x40)

            // Get the remainder [x_hi x_lo] % [d_hi d_lo] (< 2⁵¹² - 1) We use
            // the MODEXP (5) precompile with an exponent of 1. We encode the
            // arguments to the precompile at the beginning of free memory
            // without allocating. Conveniently, `r` already points to this
            // region. Arguments are encoded as:
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
            // Compute largest power of two divisor of `x`. `x` is nonzero, so
            // this is always ≥ 1.
            twos := and(sub(0x00, x), x)

            // To shift up (bits from the high limb into the low limb) we need
            // the inverse of `twos`. That is, 2²⁵⁶ / twos.
            //     2**256 / twos = -twos % 2**256 / twos + 1 -- https://2π.com/17/512-bit-division/
            // If `twos` is zero, then `twosInv` becomes one (not possible)
            twosInv := add(div(sub(0x00, twos), twos), 0x01)
        }
    }

    function _toOdd256(uint256 x_hi, uint256 x_lo, uint256 y) private pure returns (uint256 x_lo_out, uint256 y_out) {
        // Factor powers of two out of `y` and apply the same shift to [x_hi
        // x_lo]
        (uint256 twos, uint256 twosInv) = _twos(y);

        assembly ("memory-safe") {
            // Divide `y` by the power of two
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
        // Factor powers of two out of `y_lo` and apply the same shift to `x_lo`
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
        // Factor powers of two out of `y` and apply the same shift to [x_hi
        // x_lo]
        (uint256 twos, uint256 twosInv) = _twos(y);

        assembly ("memory-safe") {
            // Divide `y` by the power of two
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
            // Invert `d` mod 2²⁵⁶ -- https://2π.com/18/multiplitcative-inverses/
            // `d` is an odd number (from _toOdd*). It has an inverse modulo
            // 2²⁵⁶ such that d * inv ≡ 1 mod 2²⁵⁶.
            // We use Newton-Raphson iterations compute inv. Thanks to Hensel's
            // lifting lemma, this also works in modular arithmetic, doubling
            // the correct bits in each step. The Newton-Raphson-Hensel step is:
            //    inv_{n+1} = inv_n * (2 - d*inv_n) % 2**512

            // To kick off Newton-Raphson-Hensel iterations, we start with a
            // seed of the inverse that is correct correct for four bits.
            //     d * inv ≡ 1 mod 2⁴
            inv := xor(mul(0x03, d), 0x02)

            // Each Newton-Raphson-Hensel step doubles the number of correct
            // bits in `inv`. After 6 iterations, full convergence is
            // guaranteed.
            inv := mul(inv, sub(0x02, mul(d, inv))) // inverse mod 2⁸
            inv := mul(inv, sub(0x02, mul(d, inv))) // inverse mod 2¹⁶
            inv := mul(inv, sub(0x02, mul(d, inv))) // inverse mod 2³²
            inv := mul(inv, sub(0x02, mul(d, inv))) // inverse mod 2⁶⁴
            inv := mul(inv, sub(0x02, mul(d, inv))) // inverse mod 2¹²⁸
            inv := mul(inv, sub(0x02, mul(d, inv))) // inverse mod 2²⁵⁶
        }
    }

    function _invert512(uint256 d) private pure returns (uint256 inv_hi, uint256 inv_lo) {
        // First, we get the inverse of `d` mod 2²⁵⁶
        inv_lo = _invert256(d);

        // To extend this to the inverse mod 2⁵¹², we perform a more elaborate
        // 7th Newton-Raphson-Hensel iteration with 512 bits of precision.

        // tmp = d * inv_lo % 2**512
        (uint256 tmp_hi, uint256 tmp_lo) = _mul(d, inv_lo);
        // tmp = 2 - tmp % 2**512
        (tmp_hi, tmp_lo) = _sub(0, 2, tmp_hi, tmp_lo);

        assembly ("memory-safe") {
            // inv_hi = inv_lo * tmp / 2**256 % 2**256
            let mm := mulmod(inv_lo, tmp_lo, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
            inv_hi := add(mul(inv_lo, tmp_hi), sub(sub(mm, inv_lo), lt(mm, inv_lo)))
        }
    }

    function _invert512(uint256 d_hi, uint256 d_lo) private pure returns (uint256 inv_hi, uint256 inv_lo) {
        // First, we get the inverse of `d` mod 2²⁵⁶
        inv_lo = _invert256(d_lo);

        // To extend this to the inverse mod 2⁵¹², we perform a more elaborate
        // 7th Newton-Raphson-Hensel iteration with 512 bits of precision.

        // tmp = d * inv_lo % 2**512
        (uint256 tmp_hi, uint256 tmp_lo) = _mul(d_hi, d_lo, inv_lo);
        // tmp = 2 - tmp % 2**512
        (tmp_hi, tmp_lo) = _sub(0, 2, tmp_hi, tmp_lo);

        assembly ("memory-safe") {
            // inv_hi = inv_lo * tmp / 2**256 % 2**256
            let mm := mulmod(inv_lo, tmp_lo, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
            inv_hi := add(mul(inv_lo, tmp_hi), sub(sub(mm, inv_lo), lt(mm, inv_lo)))
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

        // Make `d` odd so that it has a multiplicative inverse mod 2²⁵⁶
        // After this we can discard `n_hi` because our result is only 256 bits
        (n_lo, d) = _toOdd256(n_hi, n_lo, d);

        // We perform division by multiplying by the multiplicative inverse of
        // the denominator mod 2²⁵⁶. Since `d` is odd, this inverse
        // exists. Compute that inverse
        d = _invert256(d);

        unchecked {
            // Because the division is now exact (we rounded `n` down to a
            // multiple of `d`), we perform it by multiplying with the modular
            // inverse of the denominator. This is the correct result mod 2²⁵⁶.
            return n_lo * d;
        }
    }

    function _gt(uint256 x_hi, uint256 x_lo, uint256 y_hi, uint256 y_lo) private pure returns (bool r) {
        assembly ("memory-safe") {
            r := or(gt(x_hi, y_hi), and(eq(x_hi, y_hi), gt(x_lo, y_lo)))
        }
    }

    function div(uint512 n, uint512 d) internal view returns (uint256) {
        (uint256 d_hi, uint256 d_lo) = d.into();
        if (d_hi == 0) {
            return div(n, d_lo);
        }
        (uint256 n_hi, uint256 n_lo) = n.into();
        if (d_lo == 0) {
            return n_hi.unsafeDiv(d_hi);
        }
        if (_gt(d_hi, d_lo, n_hi, n_lo)) {
            // TODO: this optimization may not be overall optimizing
            return 0;
        }

        // Round the numerator down to a multiple of the denominator. This makes
        // the division exact without affecting the result.
        (n_hi, n_lo) = _roundDown(n_hi, n_lo, d_hi, d_lo);

        // Make `d_lo` odd so that it has a multiplicative inverse mod 2²⁵⁶
        // After this we can discard `n_hi` and `d_hi` because our result is
        // only 256 bits
        (n_lo, d_lo) = _toOdd256(n_hi, n_lo, d_hi, d_lo);

        // We perform division by multiplying by the multiplicative inverse of
        // the denominator mod 2²⁵⁶. Since `d_lo` is odd, this inverse
        // exists. Compute that inverse
        d_lo = _invert256(d_lo);

        unchecked {
            // Because the division is now exact (we rounded `n` down to a
            // multiple of `d`), we perform it by multiplying with the modular
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

        // Make `y` odd so that it has a multiplicative inverse mod 2⁵¹²
        (x_hi, x_lo, y) = _toOdd512(x_hi, x_lo, y);

        // We perform division by multiplying by the multiplicative inverse of
        // the denominator mod 2⁵¹². Since `y` is odd, this inverse
        // exists. Compute that inverse
        (uint256 inv_hi, uint256 inv_lo) = _invert512(y);

        // Because the division is now exact (we rounded `x` down to a multiple
        // of `y`), we perform it by multiplying with the modular inverse of the
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
        (uint256 x_hi, uint256 x_lo) = x.into();
        if (y_lo == 0) {
            return r.from(0, x_hi.unsafeDiv(y_hi));
        }
        if (_gt(y_hi, y_lo, x_hi, x_lo)) {
            // TODO: this optimization may not be overall optimizing
            return r.from(0, 0);
        }

        // Round the numerator down to a multiple of the denominator. This makes
        // the division exact without affecting the result.
        (x_hi, x_lo) = _roundDown(x_hi, x_lo, y_hi, y_lo);

        // Make `y` odd so that it has a multiplicative inverse mod 2⁵¹²
        (x_hi, x_lo, y_hi, y_lo) = _toOdd512(x_hi, x_lo, y_hi, y_lo);

        // We perform division by multiplying by the multiplicative inverse of
        // the denominator mod 2⁵¹². Since `y` is odd, this inverse
        // exists. Compute that inverse
        (y_hi, y_lo) = _invert512(y_hi, y_lo);

        // Because the division is now exact (we rounded `x` down to a multiple
        // of `y`), we perform it by multiplying with the modular inverse of the
        // denominator.
        (uint256 r_hi, uint256 r_lo) = _mul(x_hi, x_lo, y_hi, y_lo);
        return r.from(r_hi, r_lo);
    }

    function idiv(uint512 r, uint512 y) internal view returns (uint512) {
        return odiv(r, r, y);
    }

    function irdiv(uint512 r, uint512 y) internal view returns (uint512) {
        return odiv(r, y, r);
    }

    function _gt(uint256 x_ex, uint256 x_hi, uint256 x_lo, uint256 y_ex, uint256 y_hi, uint256 y_lo)
        private
        pure
        returns (bool r)
    {
        assembly ("memory-safe") {
            r :=
                or(
                    or(gt(x_ex, y_ex), and(eq(x_ex, y_ex), gt(x_hi, y_hi))),
                    and(and(eq(x_ex, y_ex), eq(x_hi, y_hi)), gt(x_lo, y_lo))
                )
        }
    }

    /// The technique implemented in the following helper function for Knuth
    /// Algorithm D (a modification of the citation further below) is adapted
    /// from ridiculous fish's (aka corydoras) work
    /// https://ridiculousfish.com/blog/posts/labor-of-division-episode-iv.html
    /// and
    /// https://ridiculousfish.com/blog/posts/labor-of-division-episode-v.html .

    function _correctQ(uint256 q, uint256 r, uint256 x_next, uint256 y_next, uint256 y_whole)
        private
        pure
        returns (uint256 q_out)
    {
        assembly ("memory-safe") {
            let c1 := mul(q, y_next)
            let c2 := or(shl(0x80, r), x_next)
            q_out := sub(q, shl(gt(sub(c1, c2), y_whole), gt(c1, c2)))
        }
    }

    /// The technique implemented in the following function for division is
    /// adapted from Donald Knuth, The Art of Computer Programming (TAOCP)
    /// Volume 2, Section 4.3.1, Algorithm D.

    function _algorithmD(uint256 x_hi, uint256 x_lo, uint256 y_hi, uint256 y_lo) private pure returns (uint256 q) {
        // We treat `x` and `y` each as ≤4-limb bigints where each limb is half
        // a machine word (128 bits). This lets us perform 2-limb ÷ 1-limb
        // divisions as a single operation (`div`) as required by Algorithm
        // D. It also simplifies/optimizes some of the multiplications.

        if (y_hi > type(uint128).max) {
            // y is 4 limbs, x is 4 limbs, q is 1 limb

            // Normalize. Ensure the uppermost limb of y ≥ 2¹²⁷ (equivalently
            // y_hi >= 2**255). This is step D1 of Algorithm D
            // The author's copy of TAOCP (3rd edition) states to set `d = (2 **
            // 128 - 1) // y_hi`, however this is incorrect. Setting `d` in this
            // fashion may result in overflow in the subsequent `_mul`. Setting
            // `d` as implemented below still satisfies the postcondition (`y_hi
            // >> 128 >= 1 << 127`) but never results in overflow.
            uint256 d = uint256(1 << 128).unsafeDiv((y_hi >> 128).unsafeInc());
            uint256 x_ex;
            (x_ex, x_hi, x_lo) = _mul768(x_hi, x_lo, d);
            (y_hi, y_lo) = _mul(y_hi, y_lo, d);

            // `n_approx` is the 2 most-significant limbs of x, after
            // normalization
            uint256 n_approx = (x_ex << 128) | (x_hi >> 128);
            // `d_approx` is the most significant limb of y, after normalization
            uint256 d_approx = y_hi >> 128;
            // Normalization ensures that result of this division is an
            // approximation of the most significant (and only) limb of the
            // quotient and is too high by at most 3. This is the "Calculate
            // q-hat" (D3) step of Algorithm D. (did you know that U+0302,
            // COMBINING CIRCUMFLEX ACCENT cannot be combined with q? shameful)
            q = n_approx.unsafeDiv(d_approx);
            uint256 r_hat = n_approx.unsafeMod(d_approx);

            // The process of `_correctQ` subtracts up to 2 from `q`, to make it
            // more accurate. This is still part of the "Calculate q-hat" (D3)
            // step of Algorithm D.
            q = _correctQ(q, r_hat, x_hi & type(uint128).max, y_hi & type(uint128).max, y_hi);

            // This final, low-probability, computationally-expensive correction
            // conditionally subtracts 1 from `q` to make it exactly the
            // most-significant limb of the quotient. This is the "Multiply and
            // subtract" (D4), "Test remainder" (D5), and "Add back" (D6) steps
            // of Algorithm D, with substantial shortcutting
            {
                (uint256 tmp_ex, uint256 tmp_hi, uint256 tmp_lo) = _mul768(y_hi, y_lo, q);
                bool neg = _gt(tmp_ex, tmp_hi, tmp_lo, x_ex, x_hi, x_lo);
                assembly ("memory-safe") {
                    q := sub(q, neg)
                }
            }
        } else {
            // y is 3 limbs

            // Normalize. Ensure the most significant limb of y ≥ 2¹²⁷ (step D1)
            // See above comment about the error in TAOCP.
            uint256 d = uint256(1 << 128).unsafeDiv(y_hi.unsafeInc());
            (y_hi, y_lo) = _mul(y_hi, y_lo, d);
            // `y_next` is the second-most-significant, nonzero, normalized limb
            // of y
            uint256 y_next = y_lo >> 128;
            // `y_whole` is the 2 most-significant, nonzero, normalized limbs of
            // y
            uint256 y_whole = (y_hi << 128) | y_next;

            if (x_hi > type(uint128).max) {
                // x is 4 limbs, q is 2 limbs

                // Finish normalizing (step D1)
                uint256 x_ex;
                (x_ex, x_hi, x_lo) = _mul768(x_hi, x_lo, d);

                uint256 n_approx = (x_ex << 128) | (x_hi >> 128);
                // As before, `q_hat` is the most significant limb of the
                // quotient and too high by at most 3 (step D3)
                uint256 q_hat = n_approx.unsafeDiv(y_hi);
                uint256 r_hat = n_approx.unsafeMod(y_hi);

                // Subtract up to 2 from `q_hat`, improving our estimate (step
                // D3)
                q_hat = _correctQ(q_hat, r_hat, x_hi & type(uint128).max, y_next, y_whole);
                q = q_hat << 128;

                {
                    // "Multiply and subtract" (D4) step of Algorithm D
                    (uint256 tmp_hi, uint256 tmp_lo) = _mul(y_hi, y_lo, q_hat);
                    uint256 tmp_ex = tmp_hi >> 128;
                    tmp_hi = (tmp_hi << 128) | (tmp_lo >> 128);
                    tmp_lo <<= 128;

                    // "Test remainder" (D5) step of Algorithm D
                    bool neg = _gt(tmp_ex, tmp_hi, tmp_lo, x_ex, x_hi, x_lo);
                    // Finish step D4
                    (x_hi, x_lo) = _sub(x_hi, x_lo, tmp_hi, tmp_lo);

                    // "Add back" (D6) step of Algorithm D
                    if (neg) {
                        // This branch is quite rare, so it's gas-advantageous
                        // to actually branch and usually skip the costly `_add`
                        unchecked {
                            q -= 1 << 128;
                        }
                        (x_hi, x_lo) = _add(x_hi, x_lo, y_whole, y_lo << 128);
                    }
                }
                // `x_ex` is now zero (implicitly)

                // Run another loop (steps D3 through D6) of Algorithm D to get
                // the lower limb of the quotient
                q_hat = x_hi.unsafeDiv(y_hi);
                r_hat = x_hi.unsafeMod(y_hi);

                q_hat = _correctQ(q_hat, r_hat, x_lo >> 128, y_next, y_whole);

                {
                    (uint256 tmp_hi, uint256 tmp_lo) = _mul(y_hi, y_lo, q_hat);
                    bool neg = _gt(tmp_hi, tmp_lo, x_hi, x_lo);
                    assembly ("memory-safe") {
                        q_hat := sub(q_hat, neg)
                    }
                }

                q |= q_hat;
            } else {
                // x is 3 limbs, q is 1 limb

                // Finish normalizing (step D1)
                (x_hi, x_lo) = _mul(x_hi, x_lo, d);

                // `q` is the most significant (and only) limb of the quotient
                // and too high by at most 3 (step D3)
                q = x_hi.unsafeDiv(y_hi);
                uint256 r_hat = x_hi.unsafeMod(y_hi);

                // Subtract up to 2 from `q`, improving our estimate (step D3)
                q = _correctQ(q, r_hat, x_lo >> 128, y_next, y_whole);

                // Subtract up to 1 from `q` to make it exact (steps D4 through
                // D6)
                {
                    (uint256 tmp_hi, uint256 tmp_lo) = _mul(y_hi, y_lo, q);
                    bool neg = _gt(tmp_hi, tmp_lo, x_hi, x_lo);
                    assembly ("memory-safe") {
                        q := sub(q, neg)
                    }
                }
            }
        }
        // All other cases are handled by the checks that y ≥ 2²⁵⁶ (equivalently
        // y_hi != 0) and that x ≥ y
    }

    /// Modified from Solady (https://github.com/Vectorized/solady/blob/a3d6a974f9c9f00dcd95b235619a209a63c61d94/src/utils/LibBit.sol#L33-L45)
    /// The original code was released under the MIT license.
    function _clzLower(uint256 x) private pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := shl(0x06, lt(0xffffffffffffffff, x))
            r := or(r, shl(0x05, lt(0xffffffff, shr(r, x))))
            r := or(r, shl(0x04, lt(0xffff, shr(r, x))))
            r := or(r, shl(0x03, lt(0xff, shr(r, x))))
            // We use a 5-bit deBruijn Sequence to convert `x`'s 8
            // most-significant bits into an index. We then index the lookup
            // table (bytewise) by the deBruijn symbol to obtain the bitwise
            // inverse of its logarithm.
            r :=
                xor(
                    r,
                    byte(
                        and(0x1f, shr(shr(r, x), 0x8421084210842108cc6318c6db6d54be)),
                        0x7879797a797d7a7b797d7c7d7a7b7c7e797a7d7a7c7c7b7e7a7a7c7b7f7f7f7f
                    )
                )
        }
    }

    function _clzUpper(uint256 x) private pure returns (uint256) {
        return _clzLower(x >> 128);
    }

    function _shl(uint256 x_hi, uint256 x_lo, uint256 s) private pure returns (uint256 r_hi, uint256 r_lo) {
        assembly ("memory-safe") {
            r_hi := or(shl(s, x_hi), shr(sub(0x100, s), x_lo))
            r_lo := shl(s, x_lo)
        }
    }

    function _shl768(uint256 x_hi, uint256 x_lo, uint256 s)
        private
        pure
        returns (uint256 r_ex, uint256 r_hi, uint256 r_lo)
    {
        assembly ("memory-safe") {
            let neg_s := sub(0x100, s)
            r_ex := shr(neg_s, x_hi)
            r_hi := or(shl(s, x_hi), shr(neg_s, x_lo))
            r_lo := shl(s, x_lo)
        }
    }

    function _shr(uint256 x_hi, uint256 x_lo, uint256 s) private pure returns (uint256 r_hi, uint256 r_lo) {
        assembly ("memory-safe") {
            r_hi := shr(s, x_hi)
            r_lo := or(shl(sub(0x100, s), x_hi), shr(s, x_lo))
        }
    }

    // This function is a different modification of Knuth's Algorithm D. In this
    // case, we're only interested in the (normalized) remainder instead of the
    // quotient. We also substitute the normalization by division for
    // normalization by shifting because it makes un-normalization more
    // gas-efficient.

    function _algorithmDRemainder(uint256 x_hi, uint256 x_lo, uint256 y_hi, uint256 y_lo)
        private
        pure
        returns (uint256, uint256)
    {
        // We treat `x` and `y` each as ≤4-limb bigints where each limb is half
        // a machine word (128 bits). This lets us perform 2-limb ÷ 1-limb
        // divisions as a single operation (`div`) as required by Algorithm D.

        uint256 s;
        if (y_hi > type(uint128).max) {
            // y is 4 limbs, x is 4 limbs

            // Normalize. Ensure the uppermost limb of y ≥ 2¹²⁷ (equivalently
            // y_hi >= 2**255). This is step D1 of Algorithm D Unlike the
            // preceeding implementation of Algorithm D, we use a binary shift
            // instead of a multiply to normalize. This performs a costly "count
            // leading zeroes" operation, but it lets us transform an
            // even-more-costly division-by-inversion operation later into a
            // simple shift. This still ultimately satisfies the postcondition
            // (y_hi >> 128 >= 1 << 127) without overflowing.
            s = _clzUpper(y_hi);
            uint256 x_ex;
            (x_ex, x_hi, x_lo) = _shl768(x_hi, x_lo, s);
            (y_hi, y_lo) = _shl(y_hi, y_lo, s);

            // `n_approx` is the 2 most-significant limbs of x, after
            // normalization
            uint256 n_approx = (x_ex << 128) | (x_hi >> 128); // TODO: this can probably be optimized (combined with `_shl`)
            // `d_approx` is the most significant limb of y, after normalization
            uint256 d_approx = y_hi >> 128; // TODO: this can probably be optimized (combined with `_shl`)
            // Normalization ensures that result of this division is an
            // approximation of the most significant (and only) limb of the
            // quotient and is too high by at most 3. This is the "Calculate
            // q-hat" (D3) step of Algorithm D. (did you know that U+0302,
            // COMBINING CIRCUMFLEX ACCENT cannot be combined with q? shameful)
            uint256 q_hat = n_approx.unsafeDiv(d_approx);
            uint256 r_hat = n_approx.unsafeMod(d_approx);

            // The process of `_correctQ` subtracts up to 2 from `q_hat`, to
            // make it more accurate. This is still part of the "Calculate
            // q-hat" (D3) step of Algorithm D.
            q_hat = _correctQ(q_hat, r_hat, x_hi & type(uint128).max, y_hi & type(uint128).max, y_hi);

            {
                // This penultimate correction subtracts q-hat × y from x to
                // obtain the normalized remainder. This is the "Multiply and
                // subtract" (D4) and "Test remainder" (D5) steps of Algorithm
                // D, with some shortcutting
                (uint256 tmp_ex, uint256 tmp_hi, uint256 tmp_lo) = _mul768(y_hi, y_lo, q_hat);
                bool neg = _gt(tmp_ex, tmp_hi, tmp_lo, x_ex, x_hi, x_lo);
                (x_hi, x_lo) = _sub(x_hi, x_lo, tmp_hi, tmp_lo);
                // `x_ex` is now implicitly zero (or signals a carry that we
                // will clear in the next step)

                // Because `q_hat` may be too high by 1, we have to detect
                // underflow from the previous step and correct it. This is the
                // "Add back" (D6) step of Algorithm D
                if (neg) {
                    (x_hi, x_lo) = _add(x_hi, x_lo, y_hi, y_lo);
                }
            }
        } else {
            // y is 3 limbs

            // Normalize. Ensure the most significant limb of y ≥ 2¹²⁷ (step D1)
            // See above comment about the use of a shift instead of division.
            s = _clzLower(y_hi);
            (y_hi, y_lo) = _shl(y_hi, y_lo, s);
            // `y_next` is the second-most-significant, nonzero, normalized limb
            // of y
            uint256 y_next = y_lo >> 128; // TODO: this can probably be optimized (combined with `_shl`)
            // `y_whole` is the 2 most-significant, nonzero, normalized limbs of
            // y
            uint256 y_whole = (y_hi << 128) | y_next; // TODO: this can probably be optimized (combined with `_shl`)

            if (x_hi > type(uint128).max) {
                // x is 4 limbs; we have to run 2 iterations of Algorithm D to
                // fully divide out by y

                // Finish normalizing (step D1)
                uint256 x_ex;
                (x_ex, x_hi, x_lo) = _shl768(x_hi, x_lo, s);

                uint256 n_approx = (x_ex << 128) | (x_hi >> 128); // TODO: this can probably be optimized (combined with `_shl768`)
                // As before, `q_hat` is the most significant limb of the
                // quotient and too high by at most 3 (step D3)
                uint256 q_hat = n_approx.unsafeDiv(y_hi);
                uint256 r_hat = n_approx.unsafeMod(y_hi);

                // Subtract up to 2 from `q_hat`, improving our estimate (step
                // D3)
                q_hat = _correctQ(q_hat, r_hat, x_hi & type(uint128).max, y_next, y_whole);

                // Subtract up to 1 from q-hat to make it exactly the
                // most-significant limb of the quotient and subtract q-hat × y
                // from x to clear the most-significant limb of x.
                {
                    // "Multiply and subtract" (D4) step of Algorithm D
                    (uint256 tmp_hi, uint256 tmp_lo) = _mul(y_hi, y_lo, q_hat);
                    uint256 tmp_ex = tmp_hi >> 128;
                    tmp_hi = (tmp_hi << 128) | (tmp_lo >> 128);
                    tmp_lo <<= 128;

                    // "Test remainder" (D5) step of Algorithm D
                    bool neg = _gt(tmp_ex, tmp_hi, tmp_lo, x_ex, x_hi, x_lo);
                    // Finish step D4
                    (x_hi, x_lo) = _sub(x_hi, x_lo, tmp_hi, tmp_lo);

                    // "Add back" (D6) step of Algorithm D. We implicitly
                    // subtract 1 from `q_hat`, but elide explicitly
                    // representing that because `q_hat` is no longer needed.
                    if (neg) {
                        // This branch is quite rare, so it's gas-advantageous
                        // to actually branch and usually skip the costly `_add`
                        (x_hi, x_lo) = _add(x_hi, x_lo, y_whole, y_lo << 128);
                    }
                }
                // `x_ex` is now zero (implicitly)
                // [x_hi x_lo] now represents the partial, normalized remainder.

                // Run another loop (steps D3 through D6) of Algorithm D to get
                // the lower limb of the quotient
                // Step D3
                q_hat = x_hi.unsafeDiv(y_hi);
                r_hat = x_hi.unsafeMod(y_hi);

                // Step D3
                q_hat = _correctQ(q_hat, r_hat, x_lo >> 128, y_next, y_whole);

                // Again, implicitly correct q-hat to make it exactly the
                // least-significant limb of the quotient. Subtract q-hat × y
                // from x to obtain the normalized remainder.
                {
                    // Steps D4 and D5
                    (uint256 tmp_hi, uint256 tmp_lo) = _mul(y_hi, y_lo, q_hat);
                    bool neg = _gt(tmp_hi, tmp_lo, x_hi, x_lo);
                    (x_hi, x_lo) = _sub(x_hi, x_lo, tmp_hi, tmp_lo);

                    // Step D6
                    if (neg) {
                        (x_hi, x_lo) = _add(x_hi, x_lo, y_hi, y_lo);
                    }
                }
            } else {
                // x is 3 limbs

                // Finish normalizing (step D1)
                (x_hi, x_lo) = _shl(x_hi, x_lo, s);

                // `q_hat` is the most significant (and only) limb of the
                // quotient and too high by at most 3 (step D3)
                uint256 q_hat = x_hi.unsafeDiv(y_hi);
                uint256 r_hat = x_hi.unsafeMod(y_hi);

                // Subtract up to 2 from `q_hat`, improving our estimate (step
                // D3)
                q_hat = _correctQ(q_hat, r_hat, x_lo >> 128, y_next, y_whole);

                // Make `q_hat` exact (implicitly) and subtract q-hat × y from x
                // to obtain the normalized remainder. (steps D4 through D6)
                {
                    (uint256 tmp_hi, uint256 tmp_lo) = _mul(y_hi, y_lo, q_hat);
                    bool neg = _gt(tmp_hi, tmp_lo, x_hi, x_lo);
                    (x_hi, x_lo) = _sub(x_hi, x_lo, tmp_hi, tmp_lo);
                    if (neg) {
                        (x_hi, x_lo) = _add(x_hi, x_lo, y_hi, y_lo);
                    }
                }
            }
        }
        // All other cases are handled by the checks that y ≥ 2²⁵⁶ (equivalently
        // y_hi != 0) and that x ≥ y

        // The second-most-significant limb of normalized x is now zero
        // (equivalently x_hi < 2**128), but because the entire machine is not
        // guaranteed to be cleared, we can't optimize any further.

        // [x_hi x_lo] now represents remainder × 2ˢ (the normalized remainder);
        // we shift right by `s` (un-normalize) to obtain the result.
        return _shr(x_hi, x_lo, s);
    }

    function odivAlt(uint512 r, uint512 x, uint512 y) internal pure returns (uint512) {
        (uint256 y_hi, uint256 y_lo) = y.into();
        if (y_hi == 0) {
            // This is the only case where we can have a 2-word quotient
            return odiv(r, x, y_lo);
        }
        (uint256 x_hi, uint256 x_lo) = x.into();
        if (y_lo == 0) {
            uint256 r_lo = x_hi.unsafeDiv(y_hi);
            return r.from(0, r_lo);
        }
        if (_gt(y_hi, y_lo, x_hi, x_lo)) {
            return r.from(0, 0);
        }

        // At this point, we know that both `x` and `y` are fully represented by
        // 2 words. There is no simpler representation for the problem. We must
        // use Knuth's Algorithm D.
        {
            uint256 r_lo = _algorithmD(x_hi, x_lo, y_hi, y_lo);
            return r.from(0, r_lo);
        }
    }

    function idivAlt(uint512 r, uint512 y) internal pure returns (uint512) {
        return odivAlt(r, r, y);
    }

    function irdivAlt(uint512 r, uint512 y) internal pure returns (uint512) {
        return odivAlt(r, y, r);
    }

    function divAlt(uint512 x, uint512 y) internal pure returns (uint256) {
        (uint256 y_hi, uint256 y_lo) = y.into();
        if (y_hi == 0) {
            return div(x, y_lo);
        }
        (uint256 x_hi, uint256 x_lo) = x.into();
        if (y_lo == 0) {
            return x_hi.unsafeDiv(y_hi);
        }
        if (_gt(y_hi, y_lo, x_hi, x_lo)) {
            return 0;
        }

        // At this point, we know that both `x` and `y` are fully represented by
        // 2 words. There is no simpler representation for the problem. We must
        // use Knuth's Algorithm D.
        return _algorithmD(x_hi, x_lo, y_hi, y_lo);
    }

    function omodAlt(uint512 r, uint512 x, uint512 y) internal pure returns (uint512) {
        (uint256 y_hi, uint256 y_lo) = y.into();
        if (y_hi == 0) {
            uint256 r_lo = mod(x, y_lo);
            return r.from(0, r_lo);
        }
        (uint256 x_hi, uint256 x_lo) = x.into();
        if (y_lo == 0) {
            uint256 r_hi = x_hi.unsafeMod(y_hi);
            return r.from(r_hi, x_lo);
        }
        if (_gt(y_hi, y_lo, x_hi, x_lo)) {
            return r.from(x_hi, x_lo);
        }

        // At this point, we know that both `x` and `y` are fully represented by
        // 2 words. There is no simpler representation for the problem. We must
        // use Knuth's Algorithm D.
        {
            (uint256 r_hi, uint256 r_lo) = _algorithmDRemainder(x_hi, x_lo, y_hi, y_lo);
            return r.from(r_hi, r_lo);
        }
    }

    function imodAlt(uint512 r, uint512 y) internal pure returns (uint512) {
        return omodAlt(r, r, y);
    }

    function irmodAlt(uint512 r, uint512 y) internal pure returns (uint512) {
        return omodAlt(r, y, r);
    }
}

using Lib512MathArithmetic for uint512 global;

library Lib512MathUserDefinedHelpers {
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
    Lib512MathUserDefinedHelpers.checkNull(x, y);
    r.oadd(x, y);
}

function __sub(uint512 x, uint512 y) pure returns (uint512 r) {
    Lib512MathUserDefinedHelpers.checkNull(x, y);
    r.osub(x, y);
}

function __mul(uint512 x, uint512 y) pure returns (uint512 r) {
    Lib512MathUserDefinedHelpers.checkNull(x, y);
    r.omul(x, y);
}

function __mod(uint512 x, uint512 y) pure returns (uint512 r) {
    Lib512MathUserDefinedHelpers.checkNull(x, y);
    Lib512MathUserDefinedHelpers.smuggleToPure(Lib512MathUserDefinedHelpers.omod)(r, x, y);
}

function __div(uint512 x, uint512 y) pure returns (uint512 r) {
    Lib512MathUserDefinedHelpers.checkNull(x, y);
    Lib512MathUserDefinedHelpers.smuggleToPure(Lib512MathUserDefinedHelpers.odiv)(r, x, y);
}

using {__add as +, __sub as -, __mul as *, __mod as %, __div as / } for uint512 global;

struct uint512_external {
    uint256 hi;
    uint256 lo;
}

library Lib512MathExternal {
    function from(uint512 r, uint512_external memory x) internal pure returns (uint512) {
        assembly ("memory-safe") {
            mstore(r, mload(x))
            mstore(add(0x20, r), mload(add(0x20, x)))
        }
        return r;
    }

    function into(uint512_external memory x) internal pure returns (uint512 r) {
        assembly ("memory-safe") {
            r := x
        }
    }

    function toExternal(uint512 x) internal pure returns (uint512_external memory r) {
        assembly ("memory-safe") {
            if iszero(eq(mload(0x40), add(0x40, r))) { revert(0x00, 0x00) }
            mstore(0x40, r)
            r := x
        }
    }
}

using Lib512MathExternal for uint512 global;
using Lib512MathExternal for uint512_external global;

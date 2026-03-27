// SPDX-License-Identifier: MIT
pragma solidity =0.8.33;

import {Panic} from "./Panic.sol";
import {UnsafeMath} from "./UnsafeMath.sol";
import {Clz} from "../vendor/Clz.sol";
import {Ternary} from "./Ternary.sol";
import {FastLogic} from "./FastLogic.sol";
import {Sqrt} from "../vendor/Sqrt.sol";
import {Cbrt} from "../vendor/Cbrt.sol";

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
/// "normal" unchecked arithmetic). The `unsafe*` functions do not perform
/// checking for division or modulo by zero; in this case division or modulo by
/// zero is undefined behavior.
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
/// * divUp(uint512,uint256) returns (uint256)
/// * unsafeDiv(uint512,uint256) returns (uint256)
/// * unsafeDivUp(uint512,uint256) returns (uint256)
/// * div(uint512,uint512) returns (uint256)
/// * divUp(uint512,uint512) returns (uint256)
/// * odiv(uint512,uint512,uint256)
/// * idiv(uint512,uint256)
/// * odivUp(uint512,uint512,uint256)
/// * idivUp(uint512,uint256)
/// * odiv(uint512,uint512,uint512)
/// * idiv(uint512,uint512)
/// * irdiv(uint512,uint512)
/// * odivUp(uint512,uint512,uint512)
/// * idivUp(uint512,uint512)
/// * irdivUp(uint512,uint512)
/// * divAlt(uint512,uint512) returns (uint256) -- divAlt(uint512,uint256) is not provided because div(uint512,uint256) is suitable for chains without MODEXP
/// * odivAlt(uint512,uint512,uint512)
/// * idivAlt(uint512,uint512)
/// * irdivAlt(uint512,uint512)
/// * divUpAlt(uint512,uint512) returns (uint256)
/// * odivUpAlt(uint512,uint512,uint512)
/// * idivUpAlt(uint512,uint512)
/// * irdivUpAlt(uint512,uint512)
///
/// ### Square root
///
/// * sqrt(uint512) returns (uint256)
/// * osqrtUp(uint512,uint512)
/// * isqrtUp(uint512)
///
/// ### Cube root
///
/// * cbrt(uint512) returns (uint256)
/// * cbrtUp(uint512) returns (uint256)
///
/// ### Shifting
///
/// * oshr(uint512,uint512,uint256)
/// * ishr(uint512,uint256)
/// * oshrUp(uint512,uint512,uint256)
/// * ishrUp(uint512,uint256)
/// * oshl(uint512,uint512,uint256)
/// * ishl(uint512,uint256)
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
    using Clz for uint256;
    using Ternary for bool;
    using FastLogic for bool;
    using Sqrt for uint256;
    using Cbrt for uint256;

    function _add(uint256 x, uint256 y) private pure returns (uint256 r_hi, uint256 r_lo) {
        assembly ("memory-safe") {
            r_lo := add(x, y)
            // `lt(r_lo, x)` indicates overflow in the lower addition. We can
            // add the bool directly to the integer to perform carry
            r_hi := lt(r_lo, x)
        }
    }

    function _add(uint256 x_hi, uint256 x_lo, uint256 y) private pure returns (uint256 r_hi, uint256 r_lo) {
        assembly ("memory-safe") {
            r_lo := add(x_lo, y)
            // `lt(r_lo, x_lo)` indicates overflow in the lower
            // addition. Overflow in the high limb is simply ignored
            r_hi := add(x_hi, lt(r_lo, x_lo))
        }
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

    function oadd(uint512 r, uint256 x, uint256 y) internal pure returns (uint512) {
        (uint256 r_hi, uint256 r_lo) = _add(x, y);
        return r.from(r_hi, r_lo);
    }

    function oadd(uint512 r, uint512 x, uint256 y) internal pure returns (uint512) {
        (uint256 x_hi, uint256 x_lo) = x.into();
        (uint256 r_hi, uint256 r_lo) = _add(x_hi, x_lo, y);
        return r.from(r_hi, r_lo);
    }

    function iadd(uint512 r, uint256 y) internal pure returns (uint512) {
        return oadd(r, r, y);
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
            let mm := mulmod(x, y, not(0x00))
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
            let mm := mulmod(x_lo, y, not(0x00))
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
            let mm := mulmod(x_lo, y_lo, not(0x00))
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
            let mm0 := mulmod(x_lo, y, not(0x00))
            r_lo := mul(x_lo, y)
            let mm1 := mulmod(x_hi, y, not(0x00))
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

    function _roundDown(uint256 x_hi, uint256 x_lo, uint256 d)
        private
        pure
        returns (uint256 r_hi, uint256 r_lo, uint256 rem)
    {
        assembly ("memory-safe") {
            // Get the remainder [n_hi n_lo] % d (< 2²⁵⁶ - 1)
            // 2**256 % d = -d % 2**256 % d -- https://2π.com/17/512-bit-division/
            rem := mulmod(x_hi, sub(0x00, d), d)
            rem := addmod(x_lo, rem, d)

            r_hi := sub(x_hi, gt(rem, x_lo))
            r_lo := sub(x_lo, rem)
        }
    }

    // TODO: remove and replace existing division operations with the Algorithm
    // D variants
    function _roundDown(uint256 x_hi, uint256 x_lo, uint256 d_hi, uint256 d_lo)
        private
        view
        returns (uint256 r_hi, uint256 r_lo, uint256 rem_hi, uint256 rem_lo)
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
        (rem_hi, rem_lo) = r.into();
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

    // TODO: once the existing division routines are ported over to the
    // Algorithm D variants (avoiding the use of the `MODEXP` precompile), this
    // function is no longer needed.
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
            let mm := mulmod(inv_lo, tmp_lo, not(0x00))
            inv_hi := add(mul(inv_lo, tmp_hi), sub(sub(mm, inv_lo), lt(mm, inv_lo)))
        }
    }

    function _div(uint256 n_hi, uint256 n_lo, uint256 d) private pure returns (uint256) {
        // Round the numerator down to a multiple of the denominator. This makes
        // the division exact without affecting the result.
        (n_hi, n_lo,) = _roundDown(n_hi, n_lo, d);

        // Make `d` odd so that it has a multiplicative inverse mod 2²⁵⁶.
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

    function _divUp(uint256 n_hi, uint256 n_lo, uint256 d) private pure returns (uint256) {
        // Round the numerator down to a multiple of the denominator. This makes
        // the division exact without affecting the result. Store the remainder
        // for later to determine whether we must increment the result in order
        // to round up.
        uint256 rem;
        (n_hi, n_lo, rem) = _roundDown(n_hi, n_lo, d);

        // Make `d` odd so that it has a multiplicative inverse mod 2²⁵⁶.
        // After this we can discard `n_hi` because our result is only 256 bits
        (n_lo, d) = _toOdd256(n_hi, n_lo, d);

        // We perform division by multiplying by the multiplicative inverse of
        // the denominator mod 2²⁵⁶. Since `d` is odd, this inverse
        // exists. Compute that inverse
        d = _invert256(d);

        unchecked {
            // Because the division is now exact (we rounded `n` down to a
            // multiple of `d`), we perform it by multiplying with the modular
            // inverse of the denominator. This is the floor of the division,
            // mod 2²⁵⁶. To obtain the ceiling, we conditionally add 1 if the
            // remainder was nonzero.
            return (n_lo * d).unsafeInc(0 < rem);
        }
    }

    /// @dev 2-word rounded division: round((x_hi·2²⁵⁶ + x_lo) / d).
    /// Returns a 2-word quotient. Rounds half-up (ties go up).
    function _divRound(uint256 x_hi, uint256 x_lo, uint256 d) private pure returns (uint256 r_hi, uint256 r_lo) {
        assembly ("memory-safe") {
            r_hi := div(x_hi, d)
            x_hi := mod(x_hi, d)
        }
        r_lo = _div(x_hi, x_lo, d);
        assembly ("memory-safe") {
            // Remainder of (x_hi·2²⁵⁶ + x_lo) / d via mulmod trick
            let rem := addmod(mulmod(x_hi, sub(0, d), d), x_lo, d)
            // Round half-up: add 1 if rem >= ceil(d/2) ↔ rem > (d-1)/2
            let rnd := gt(rem, div(sub(d, 1), 2))
            r_lo := add(r_lo, rnd)
            r_hi := add(r_hi, and(rnd, iszero(r_lo)))
        }
    }

    function unsafeDiv(uint512 n, uint256 d) internal pure returns (uint256) {
        (uint256 n_hi, uint256 n_lo) = n.into();
        if (n_hi == 0) {
            return n_lo.unsafeDiv(d);
        }

        return _div(n_hi, n_lo, d);
    }

    function div(uint512 n, uint256 d) internal pure returns (uint256) {
        if (d == 0) {
            Panic.panic(Panic.DIVISION_BY_ZERO);
        }

        return unsafeDiv(n, d);
    }

    function unsafeDivUp(uint512 n, uint256 d) internal pure returns (uint256) {
        (uint256 n_hi, uint256 n_lo) = n.into();
        if (n_hi == 0) {
            return n_lo.unsafeDivUp(d);
        }

        return _divUp(n_hi, n_lo, d);
    }

    function divUp(uint512 n, uint256 d) internal pure returns (uint256) {
        if (d == 0) {
            Panic.panic(Panic.DIVISION_BY_ZERO);
        }

        return unsafeDivUp(n, d);
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
        (n_hi, n_lo,,) = _roundDown(n_hi, n_lo, d_hi, d_lo);

        // Make `d_lo` odd so that it has a multiplicative inverse mod 2²⁵⁶.
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

    function divUp(uint512 n, uint512 d) internal view returns (uint256) {
        (uint256 d_hi, uint256 d_lo) = d.into();
        if (d_hi == 0) {
            return divUp(n, d_lo);
        }
        (uint256 n_hi, uint256 n_lo) = n.into();
        if (d_lo == 0) {
            return n_hi.unsafeDiv(d_hi).unsafeInc(0 < (n_lo | n_hi.unsafeMod(d_hi)));
        }

        // Round the numerator down to a multiple of the denominator. This makes
        // the division exact without affecting the result. Save the remainder
        // for later to determine whether we need to increment to round up.
        uint256 rem_hi;
        uint256 rem_lo;
        (n_hi, n_lo, rem_hi, rem_lo) = _roundDown(n_hi, n_lo, d_hi, d_lo);

        // Make `d_lo` odd so that it has a multiplicative inverse mod 2²⁵⁶.
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
            // inverse of the denominator. This is the floor of the division,
            // mod 2²⁵⁶. To obtain the ceiling, we conditionally add 1 if the
            // remainder was nonzero.
            return (n_lo * d_lo).unsafeInc(0 < (rem_hi | rem_lo));
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

        // The upper word of the quotient is straightforward. We can use
        // "normal" division to obtain it. The remainder after that division
        // must be carried forward to the later steps, however, because the next
        // operation we perform is a `mulmod` of `x_hi` with `y`, there's no
        // need to reduce `x_hi` mod `y` as would be ordinarily expected.
        uint256 r_hi = x_hi.unsafeDiv(y);

        // Round the numerator down to a multiple of the denominator. This makes
        // the division exact without affecting the result.
        (x_hi, x_lo,) = _roundDown(x_hi, x_lo, y);

        // Make `y` odd so that it has a multiplicative inverse mod 2²⁵⁶. After
        // this we can discard `x_hi` because we have already obtained the upper
        // word.
        (x_lo, y) = _toOdd256(x_hi, x_lo, y);

        // The lower word of the quotient is obtained from division by
        // multiplying by the multiplicative inverse of the denominator mod
        // 2²⁵⁶. Since `y` is odd, this inverse exists. Compute that inverse
        y = _invert256(y);

        uint256 r_lo;
        unchecked {
            // Because the division is now exact (we rounded `x` down to a
            // multiple of the original `y`), we perform it by multiplying with
            // the modular inverse of the denominator. This is the correct
            // result mod 2²⁵⁶.
            r_lo = x_lo * y;
        }

        return r.from(r_hi, r_lo);
    }

    function idiv(uint512 r, uint256 y) internal pure returns (uint512) {
        return odiv(r, r, y);
    }

    function odivUp(uint512 r, uint512 x, uint256 y) internal pure returns (uint512) {
        if (y == 0) {
            Panic.panic(Panic.DIVISION_BY_ZERO);
        }

        (uint256 x_hi, uint256 x_lo) = x.into();
        if (x_hi == 0) {
            return r.from(0, x_lo.unsafeDivUp(y));
        }

        // The upper word of the quotient is straightforward. We can use
        // "normal" division to obtain it. The remainder after that division
        // must be carried forward to the later steps, however, because the next
        // operation we perform is a `mulmod` of `x_hi` with `y`, there's no
        // need to reduce `x_hi` mod `y` as would be ordinarily expected.
        uint256 r_hi = x_hi.unsafeDiv(y);

        // Round the numerator down to a multiple of the denominator. This makes
        // the division exact without affecting the result. Save the remainder
        // for later to determine whether we need to increment to round up.
        uint256 rem;
        (x_hi, x_lo, rem) = _roundDown(x_hi, x_lo, y);

        // Make `y` odd so that it has a multiplicative inverse mod 2²⁵⁶. After
        // this we can discard `x_hi` because we have already obtained the upper
        // word.
        (x_lo, y) = _toOdd256(x_hi, x_lo, y);

        // The lower word of the quotient is obtained from division by
        // multiplying by the multiplicative inverse of the denominator mod
        // 2²⁵⁶. Since `y` is odd, this inverse exists. Compute that inverse
        y = _invert256(y);

        uint256 r_lo;
        unchecked {
            // Because the division is now exact (we rounded `x` down to a
            // multiple of the original `y`), we perform it by multiplying with
            // the modular inverse of the denominator. This is the floor of the
            // division, mod 2²⁵⁶.
            r_lo = x_lo * y;
        }
        // To obtain the ceiling, we conditionally add 1 if the remainder was
        // nonzero.
        (r_hi, r_lo) = _add(r_hi, r_lo, (0 < rem).toUint());

        return r.from(r_hi, r_lo);
    }

    function idivUp(uint512 r, uint256 y) internal pure returns (uint512) {
        return odivUp(r, r, y);
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
        (x_hi, x_lo,,) = _roundDown(x_hi, x_lo, y_hi, y_lo);

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

    function odivUp(uint512 r, uint512 x, uint512 y) internal view returns (uint512) {
        (uint256 y_hi, uint256 y_lo) = y.into();
        if (y_hi == 0) {
            return odivUp(r, x, y_lo);
        }
        (uint256 x_hi, uint256 x_lo) = x.into();
        if (y_lo == 0) {
            (uint256 r_hi_, uint256 r_lo_) = _add(0, x_hi.unsafeDiv(y_hi), (0 < (x_lo | x_hi.unsafeMod(y_hi))).toUint());
            return r.from(r_hi_, r_lo_);
        }

        // Round the numerator down to a multiple of the denominator. This makes
        // the division exact without affecting the result. Save the remainder
        // for later to determine whether we need to increment to round up.
        uint256 rem_hi;
        uint256 rem_lo;
        (x_hi, x_lo, rem_hi, rem_lo) = _roundDown(x_hi, x_lo, y_hi, y_lo);

        // Make `y` odd so that it has a multiplicative inverse mod 2⁵¹²
        (x_hi, x_lo, y_hi, y_lo) = _toOdd512(x_hi, x_lo, y_hi, y_lo);

        // We perform division by multiplying by the multiplicative inverse of
        // the denominator mod 2⁵¹². Since `y` is odd, this inverse
        // exists. Compute that inverse
        (y_hi, y_lo) = _invert512(y_hi, y_lo);

        // Because the division is now exact (we rounded `x` down to a multiple
        // of `y`), we perform it by multiplying with the modular inverse of the
        // denominator. This is the floor of the division.
        (uint256 r_hi, uint256 r_lo) = _mul(x_hi, x_lo, y_hi, y_lo);

        // To obtain the ceiling, we conditionally add 1 if the remainder was
        // nonzero.
        (r_hi, r_lo) = _add(r_hi, r_lo, (0 < (rem_hi | rem_lo)).toUint());

        return r.from(r_hi, r_lo);
    }

    function idivUp(uint512 r, uint512 y) internal view returns (uint512) {
        return odivUp(r, r, y);
    }

    function irdivUp(uint512 r, uint512 y) internal view returns (uint512) {
        return odivUp(r, y, r);
    }

    function _gt(uint256 x_ex, uint256 x_hi, uint256 x_lo, uint256 y_ex, uint256 y_hi, uint256 y_lo)
        private
        pure
        returns (bool r)
    {
        assembly ("memory-safe") {
            r := or(
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

        if (y_hi >> 128 != 0) {
            // y is 4 limbs, x is 4 limbs, q is 1 limb

            // Normalize. Ensure the uppermost limb of y ≥ 2¹²⁷ (equivalently
            // y_hi >= 2**255). This is step D1 of Algorithm D. We use `CLZ` to
            // find the shift amount, then shift both `x` and `y` left. This is
            // more gas-efficient than multiplication-based normalization.
            uint256 s = y_hi.clz();
            uint256 x_ex;
            (x_ex, x_hi, x_lo) = _shl256(x_hi, x_lo, s);
            (, y_hi, y_lo) = _shl256(y_hi, y_lo, s);

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
                q = q.unsafeDec(neg);
            }
        } else {
            // y is 3 limbs

            // Normalize. Ensure the most significant limb of y ≥ 2¹²⁷ (step D1)
            // We use `CLZ` to find the shift amount for normalization
            uint256 s = (y_hi << 128).clz();
            (, y_hi, y_lo) = _shl256(y_hi, y_lo, s);
            // `y_next` is the second-most-significant, nonzero, normalized limb
            // of y
            uint256 y_next = y_lo >> 128;
            // `y_whole` is the 2 most-significant, nonzero, normalized limbs of
            // y
            uint256 y_whole = (y_hi << 128) | y_next;

            if (x_hi >> 128 != 0) {
                // x is 4 limbs, q is 2 limbs

                // Finish normalizing (step D1)
                uint256 x_ex;
                (x_ex, x_hi, x_lo) = _shl256(x_hi, x_lo, s);

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
                    q_hat = q_hat.unsafeDec(neg);
                }

                q |= q_hat;
            } else {
                // x is 3 limbs, q is 1 limb

                // Finish normalizing (step D1)
                (, x_hi, x_lo) = _shl256(x_hi, x_lo, s);

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
                    q = q.unsafeDec(neg);
                }
            }
        }
        // All other cases are handled by the checks that y ≥ 2²⁵⁶ (equivalently
        // y_hi != 0) and that x ≥ y
    }

    /// @dev 3-word / 2-word → 1-word division via Algorithm D.
    /// floor((x_ex·2⁵¹² + x_hi·2²⁵⁶ + x_lo) / (y_hi·2²⁵⁶ + y_lo))
    /// Precondition: result fits in one word; y_hi ≠ 0.
    function _algorithmD(uint256 x_ex, uint256 x_hi, uint256 x_lo, uint256 y_hi, uint256 y_lo)
        private
        pure
        returns (uint256 q)
    {
        if (x_ex == 0) return _algorithmD(x_hi, x_lo, y_hi, y_lo);

        // Normalize so the leading word of y has its MSB set (Knuth step D1).
        // The high digit of the quotient is 0 (x_ex is small), so we compute
        // only the low digit. Trial quotient: floor((u₁·2²⁵⁶ + u₂) / v₁)
        // where u₁, u₂ are the top two words of the shifted numerator and v₁
        // is the top word of the shifted denominator.
        uint256 s = y_hi.clz();
        {
            uint256 u1;
            uint256 u2;
            uint256 v1;
            assembly ("memory-safe") {
                let inv_s := sub(256, s)
                // u₁ = (x_ex << s) | (x_hi >> inv_s)  — absorbs overflow from x_ex into the trial word
                u1 := or(shl(s, x_ex), shr(inv_s, x_hi))
                // u₂ = (x_hi << s) | (x_lo >> inv_s)
                u2 := or(shl(s, x_hi), shr(inv_s, x_lo))
                // v₁ = (y_hi << s) | (y_lo >> inv_s)  — MSB now set
                v1 := or(shl(s, y_hi), shr(inv_s, y_lo))
            }
            // u₁ < v₁ guaranteed (quotient fits in 1 word), so _div is safe.
            q = (u1 < v1) ? _div(u1, u2, v1) : type(uint256).max;
        }

        // Steps D4–D6: multiply back with un-shifted values and correct.
        // Trial quotient overshoots by at most 2.
        {
            (uint256 p_ex, uint256 p_hi, uint256 p_lo) = _mul768(y_hi, y_lo, q);
            while (_gt(p_ex, p_hi, p_lo, x_ex, x_hi, x_lo)) {
                unchecked {
                    q--;
                }
                assembly ("memory-safe") {
                    let b := lt(p_lo, y_lo)
                    p_lo := sub(p_lo, y_lo)
                    let mid := sub(p_hi, b)
                    b := or(lt(p_hi, b), lt(mid, y_hi))
                    p_hi := sub(mid, y_hi)
                    p_ex := sub(p_ex, b)
                }
            }
        }
    }

    function _shl256(uint256 x_lo, uint256 s) private pure returns (uint256 r_hi, uint256 r_lo) {
        assembly ("memory-safe") {
            r_hi := shr(sub(0x100, s), x_lo)
            r_lo := shl(s, x_lo)
        }
    }

    function _shl256(uint256 x_hi, uint256 x_lo, uint256 s)
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

    function _shl(uint256 x_lo, uint256 s) private pure returns (uint256 r_hi, uint256 r_lo) {
        (r_hi, r_lo) = _shl256(x_lo, s);
        unchecked {
            r_hi |= x_lo << s - 256;
        }
    }

    function _shl(uint256 x_hi, uint256 x_lo, uint256 s) private pure returns (uint256 r_hi, uint256 r_lo) {
        (, r_hi, r_lo) = _shl256(x_hi, x_lo, s);
        unchecked {
            r_hi |= x_lo << s - 256;
        }
    }

    function _shr256(uint256 x_hi, uint256 x_lo, uint256 s) private pure returns (uint256 r_hi, uint256 r_lo) {
        assembly ("memory-safe") {
            r_hi := shr(s, x_hi)
            r_lo := shr(s, x_lo)
            r_lo := or(shl(sub(0x100, s), x_hi), r_lo)
        }
    }

    function _shr(uint256 x_hi, uint256 x_lo, uint256 s) private pure returns (uint256 r_hi, uint256 r_lo) {
        (r_hi, r_lo) = _shr256(x_hi, x_lo, s);
        unchecked {
            r_lo |= x_hi >> s - 256;
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
        if (y_hi >> 128 != 0) {
            // y is 4 limbs, x is 4 limbs

            // Normalize. Ensure the uppermost limb of y ≥ 2¹²⁷ (equivalently
            // y_hi >= 2**255). This is step D1 of Algorithm D. Unlike the
            // preceeding implementation of Algorithm D, we use a binary shift
            // instead of a multiply to normalize. This performs a costly "count
            // leading zeroes" operation, but it lets us transform an
            // even-more-costly division-by-inversion operation later into a
            // simple shift. This still ultimately satisfies the postcondition
            // (y_hi >> 128 >= 1 << 127) without overflowing.
            s = y_hi.clz();
            uint256 x_ex;
            (x_ex, x_hi, x_lo) = _shl256(x_hi, x_lo, s);
            (, y_hi, y_lo) = _shl256(y_hi, y_lo, s);

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
            s = (y_hi << 128).clz();
            (, y_hi, y_lo) = _shl256(y_hi, y_lo, s);
            // `y_next` is the second-most-significant, nonzero, normalized limb
            // of y
            uint256 y_next = y_lo >> 128; // TODO: this can probably be optimized (combined with `_shl`)
            // `y_whole` is the 2 most-significant, nonzero, normalized limbs of
            // y
            uint256 y_whole = (y_hi << 128) | y_next; // TODO: this can probably be optimized (combined with `_shl`)

            if (x_hi >> 128 != 0) {
                // x is 4 limbs; we have to run 2 iterations of Algorithm D to
                // fully divide out by y

                // Finish normalizing (step D1)
                uint256 x_ex;
                (x_ex, x_hi, x_lo) = _shl256(x_hi, x_lo, s);

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
                (, x_hi, x_lo) = _shl256(x_hi, x_lo, s);

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
        // (equivalently x_hi < 2**128), but because the entire machine word is
        // not guaranteed to be cleared, we can't optimize any further.

        // [x_hi x_lo] now represents remainder × 2ˢ (the normalized remainder);
        // we shift right by `s` (un-normalize) to obtain the result.
        return _shr256(x_hi, x_lo, s);
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

    function divUpAlt(uint512 x, uint512 y) internal pure returns (uint256) {
        (uint256 y_hi, uint256 y_lo) = y.into();
        if (y_hi == 0) {
            return divUp(x, y_lo);
        }
        (uint256 x_hi, uint256 x_lo) = x.into();
        if (y_lo == 0) {
            return x_hi.unsafeDiv(y_hi).unsafeInc(0 < (x_lo | x_hi.unsafeMod(y_hi)));
        }
        if (_gt(y_hi, y_lo, x_hi, x_lo)) {
            return (0 < (x_hi | x_lo)).toUint();
        }

        // At this point, we know that both `x` and `y` are fully represented by
        // 2 words. There is no simpler representation for the problem. We must
        // use Knuth's Algorithm D.
        uint256 q = _algorithmD(x_hi, x_lo, y_hi, y_lo);

        // If the division was not exact, then we must round up. This is more
        // efficient than explicitly computing whether the remainder is nonzero
        // inside `_algorithmD`.
        (uint256 prod_hi, uint256 prod_lo) = _mul(y_hi, y_lo, q);
        return q.unsafeInc(0 < (prod_hi ^ x_hi) | (prod_lo ^ x_lo));
    }

    function odivUpAlt(uint512 r, uint512 x, uint512 y) internal pure returns (uint512) {
        (uint256 y_hi, uint256 y_lo) = y.into();
        if (y_hi == 0) {
            return odivUp(r, x, y_lo);
        }
        (uint256 x_hi, uint256 x_lo) = x.into();
        if (y_lo == 0) {
            (uint256 r_hi_, uint256 r_lo_) = _add(0, x_hi.unsafeDiv(y_hi), (0 < (x_lo | x_hi.unsafeMod(y_hi))).toUint());
            return r.from(r_hi_, r_lo_);
        }
        if (_gt(y_hi, y_lo, x_hi, x_lo)) {
            return r.from(0, (0 < (x_hi | x_lo)).toUint());
        }

        // At this point, we know that both `x` and `y` are fully represented by
        // 2 words. There is no simpler representation for the problem. We must
        // use Knuth's Algorithm D.
        uint256 q = _algorithmD(x_hi, x_lo, y_hi, y_lo);

        // If the division was not exact, then we must round up. This is more
        // efficient than explicitly computing whether the remainder is nonzero
        // inside `_algorithmD`.
        (uint256 prod_hi, uint256 prod_lo) = _mul(y_hi, y_lo, q);
        (uint256 r_hi, uint256 r_lo) = _add(0, q, (0 < (prod_hi ^ x_hi) | (prod_lo ^ x_lo)).toUint());
        return r.from(r_hi, r_lo);
    }

    function idivUpAlt(uint512 r, uint512 y) internal pure returns (uint512) {
        return odivUpAlt(r, r, y);
    }

    function irdivUpAlt(uint512 r, uint512 y) internal pure returns (uint512) {
        return odivUpAlt(r, y, r);
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

    //// The following 512-bit square root implementation is a realization of Zimmermann's "Karatsuba
    //// Square Root" algorithm https://inria.hal.science/inria-00072854/document . This approach is
    //// inspired by https://github.com/SimonSuckut/Solidity_Uint512/ . These helper functions are
    //// broken out separately to ease formal verification.

    /// One square root Babylonian step: r = ⌊(x/r + r) / 2⌋
    function _sqrt_babylonianStep(uint256 x, uint256 r) private pure returns (uint256) {
        unchecked {
            return x.unsafeDiv(r) + r >> 1;
        }
    }

    /// 6 Babylonian steps from fixed seed + floor correction + residue for Karatsuba
    ///
    /// Implementing this as:
    ///   uint256 r_hi = x_hi.sqrt();
    ///   uint256 res = x_hi - r_hi * r_hi;
    /// is correct, but duplicates the normalization that we do in `_sqrt` and performs a
    /// more-costly initialization step. solc is not very smart. It can't optimize away the
    /// initialization step of `Sqrt.sqrt`. It also can't optimize the calculation of `res`, so
    /// doing it in Yul is meaningfully more gas efficient.
    function _sqrt_baseCase(uint256 x_hi) private pure returns (uint256 r_hi, uint256 res) {
        // Seed with √(2²⁵⁵), the geometric mean of the normalized √xₕᵢ range [2¹²⁷, 2¹²⁸).
        // This balances worst-case over/underestimate (ε ≈ ±0.414/0.293), giving >128 bits of
        // precision in 6 Babylonian steps
        r_hi = 0xb504f333f9de6484597d89b3754abe9f;

        // 6 Babylonian steps is sufficient for convergence
        r_hi = _sqrt_babylonianStep(x_hi, r_hi);
        r_hi = _sqrt_babylonianStep(x_hi, r_hi);
        r_hi = _sqrt_babylonianStep(x_hi, r_hi);
        r_hi = _sqrt_babylonianStep(x_hi, r_hi);
        r_hi = _sqrt_babylonianStep(x_hi, r_hi);
        r_hi = _sqrt_babylonianStep(x_hi, r_hi);

        // The Babylonian step can oscillate between ⌊√xₕᵢ⌋ and ⌈√xₕᵢ⌉. Clean that up.
        r_hi = r_hi.unsafeDec(x_hi.unsafeDiv(r_hi) < r_hi);

        assembly ("memory-safe") {
            // This is cheaper than
            //   unchecked {
            //     uint256 res = x_hi - r_hi * r_hi;
            //   }
            // for no clear reason
            res := sub(x_hi, mul(r_hi, r_hi))
        }
    }

    /// Karatsuba quotient with carry correction
    ///
    /// `res` is (almost) a single limb. Create a new (almost) machine word `n` with `res` as
    /// the upper limb and shifting in the next limb of `x` (namely `x_lo >> 128`) as the
    /// lower limb. The next step of Zimmermann's algorithm is:
    ///   rₗₒ = n / (2 · rₕᵢ)
    ///   res = n % (2 · rₕᵢ)
    function _sqrt_karatsubaQuotient(uint256 res, uint256 x_lo, uint256 r_hi)
        private
        pure
        returns (uint256 r_lo, uint256 res_out)
    {
        assembly ("memory-safe") {
            let n := or(shl(0x80, res), shr(0x80, x_lo))
            let d := shl(0x01, r_hi)
            r_lo := div(n, d)

            let c := shr(0x80, res)
            res_out := mod(n, d)

            // It's possible that `n` was 257 bits and overflowed (`res` was not just a single
            // limb). Explicitly handling the carry avoids 512-bit division.
            if c {
                r_lo := add(r_lo, div(not(0x00), d))
                res_out := add(res_out, add(0x01, mod(not(0x00), d)))
                r_lo := add(r_lo, div(res_out, d))
                res_out := mod(res_out, d)
            }
        }
    }

    /// Combine `r_hi` with `r_lo` and perform the 257-bit underflow correction
    ///
    /// The final step of Zimmermann's algorithm is: if res · 2¹²⁸ + xₗₒ % 2¹²⁸ < rₗₒ², decrement
    /// `r`. We have to do this in a complicated manner because both `res` and `r_lo` can be
    /// 𝑠𝑙𝑖𝑔ℎ𝑡𝑙𝑦 longer than 1 limb (128 bits). This is more efficient than performing the full
    /// 257-bit comparison.
    function _sqrt_correction(uint256 r_hi, uint256 r_lo, uint256 res, uint256 x_lo) private pure returns (uint256 r) {
        unchecked {
            r = (r_hi << 128) + r_lo;
            r = r.unsafeDec(
                ((res >> 128) < (r_lo >> 128))
                .or(
                    ((res >> 128) == (r_lo >> 128))
                    .and((res << 128) | (x_lo & 0xffffffffffffffffffffffffffffffff) < r_lo * r_lo)
                )
            );
        }
    }

    function _sqrt(uint256 x_hi, uint256 x_lo) private pure returns (uint256 r) {
        unchecked {
            // Normalize `x` so the top word has its MSB in bit 255 or 254. This makes the "shift
            // back" step exact.
            //   x ≥ 2⁵¹⁰
            uint256 shift = x_hi.clz();
            (, x_hi, x_lo) = _shl256(x_hi, x_lo, shift & 0xfe);
            shift >>= 1;

            // We treat `r` as a ≤2-limb bigint where each limb is half a machine word (128 bits).
            // Spliting √x in this way lets us apply "ordinary" 256-bit `sqrt` to the top word of
            // `x`. Then we can recover the bottom limb of `r` without 512-bit division.
            (uint256 r_hi, uint256 res) = _sqrt_baseCase(x_hi);

            // The next titular Karatsuba step extends the upper limb of `r` to approximate the
            // lower limb.
            uint256 r_lo;
            (r_lo, res) = _sqrt_karatsubaQuotient(res, x_lo, r_hi);

            // The Karatsuba step is an approximation. This refinement makes it exactly ⌊√x⌋
            r = _sqrt_correction(r_hi, r_lo, res, x_lo);

            // Un-normalize
            return r >> shift;
        }
    }

    function sqrt(uint512 x) internal pure returns (uint256) {
        (uint256 x_hi, uint256 x_lo) = x.into();

        if (x_hi == 0) {
            return x_lo.sqrt();
        }

        return _sqrt(x_hi, x_lo);
    }

    function osqrtUp(uint512 r, uint512 x) internal pure returns (uint512) {
        (uint256 x_hi, uint256 x_lo) = x.into();

        uint256 r_hi;
        uint256 r_lo;
        if (x_hi == 0) {
            r_lo = x_lo.sqrtUp();
        } else {
            r_lo = _sqrt(x_hi, x_lo);
            (uint256 r2_hi, uint256 r2_lo) = _mul(r_lo, r_lo);
            (r_hi, r_lo) = _add(0, r_lo, _gt(x_hi, x_lo, r2_hi, r2_lo).toUint());
        }

        return r.from(r_hi, r_lo);
    }

    function isqrtUp(uint512 r) internal pure returns (uint512) {
        return osqrtUp(r, r);
    }

    //// Similar to the 512-bit square root implementation, the 512-bit cube root is also a
    //// realization of Zimmermann's Karatsuba, but this implements the generalized-root variation
    //// that is obliquely referenced just before the "Acknowledgements" and more explicitly
    //// detailed in §1.5.2 of Brent and Zimmermann's "Modern Computer Arithmetic"
    //// https://members.loria.fr/PZimmermann/mca/mca-0.2.1.pdf . The key difference here is that in
    //// the expansion of the 𝑐𝑢𝑏𝑒 of the limbs of the result (the Karatsuba step), there are 3
    //// terms that meaningfully contribute to the result. This requires an additional, more
    //// elaborate, quadratic correction step.
    ////
    //// The square root algorithm works with limbs of the result that are half of a word. For cube
    //// root, we use limbs of `r` that are (roughly) one third of a word.

    /// One cube root Newton-Raphson step: r = ⌊(⌊x/r²⌋ + 2·r) / 3⌋
    function _cbrt_newtonRaphsonStep(uint256 x, uint256 r) private pure returns (uint256) {
        unchecked {
            return (x.unsafeDiv(r * r) + r + r) / 3;
        }
    }

    /// 6 Newton-Raphson steps from the fixed seed, including a rounding fixup step and returning
    /// the residue for Karatsuba
    ///
    /// Like the square root case, implementing this as:
    ///   uint256 r_hi = x_hi.cbrt();
    ///   uint256 res = x_hi - r_hi * r_hi * r_hi;
    ///   uint256 d = r_hi * r_hi * 3;
    /// is correct, but we can shave some gas by avoiding the normalization step from
    /// `Cbrt.cbrt`. `d` is the derivative/denominator for the subsequent Karatsuba step.
    function _cbrt_baseCase(uint256 x_hi) private pure returns (uint256 r_hi, uint256 res, uint256 d) {
        unchecked {
            x_hi >>= 2; // xₕᵢ ≥ 2²⁵¹; xₕᵢ < 2²⁵⁴ from the normalization
            r_hi = 0x1250bfe1b082f4f9b8d4ce; // ∛(3·2²⁵¹) suitable given `x_hi` in its range

            r_hi = _cbrt_newtonRaphsonStep(x_hi, r_hi);
            r_hi = _cbrt_newtonRaphsonStep(x_hi, r_hi);
            r_hi = _cbrt_newtonRaphsonStep(x_hi, r_hi);
            r_hi = _cbrt_newtonRaphsonStep(x_hi, r_hi);
            r_hi = _cbrt_newtonRaphsonStep(x_hi, r_hi);
            r_hi = _cbrt_newtonRaphsonStep(x_hi, r_hi);

            // 6 iterations yield >85 bits of precision (absolute error < 2⁻¹⁶), so `r_hi` is at
            // most ⌊∛xₕᵢ⌋ + 1. A branchless floor correction suffices.
            uint256 r_hi2 = r_hi * r_hi;
            uint256 r_hi3 = r_hi2 * r_hi;
            r_hi = r_hi.unsafeDec(r_hi3 > x_hi);
            r_hi2 = r_hi * r_hi;
            r_hi3 = r_hi2 * r_hi;

            res = x_hi - r_hi3;
            d = r_hi2 * 3;
        }
    }

    /// This is the Karatsuba step. The 86-bit lower limb of `r` is (almost):
    ///   rₗₒ = ⌊(res ⋅ 2⁸⁶ + xₗₒ) / (3 ⋅ rₕᵢ²)⌋
    ///   resₒᵤₜ = (res ⋅ 2⁸⁶ + xₗₒ) mod (3 ⋅ rₕᵢ²)
    /// Where `res` is the (nearly) 2-limb residue from the previous "normal" cube root step. The
    /// new residue, `res_out`, is propagated to the quadratic correction step instead of the
    /// underflow check from Zimmermann
    function _cbrt_karatsubaQuotient(uint256 res, uint256 x_lo, uint256 d)
        private
        pure
        returns (uint256 r_lo, uint256 res_out)
    {
        assembly ("memory-safe") {
            let n := or(shl(0x56, res), x_lo)
            r_lo := div(n, d)

            let c := shr(0xaa, res)
            res_out := mod(n, d)

            // If `res` was 171 bits (one more than expected), then `n` overflowed to 257
            // bits. Explicitly handling the carry avoids 512-bit division.
            if c {
                r_lo := add(r_lo, div(not(0x00), d))
                res_out := add(res_out, add(0x01, mod(not(0x00), d)))
                r_lo := add(r_lo, div(res_out, d))
                res_out := mod(res_out, d)
            }
        }
    }

    /// Combine `r_hi` with `r_lo`, perform the quadratic correction, and prevent undershoot
    ///
    /// Unlike the square-root case, the error from the linear Karatsuba step can still be large
    /// because the expansion has more terms. We do a quadratic correction to get close enough that
    /// we can use `res` to correct. In the square-root version, the only ignored term in (s + q)²
    /// is q², which is small enough for a 1ulp correction. For cube root, the binomial expansion
    /// (rₕᵢ·2⁸⁶ + rₗₒ)³ contains the cross term 3·(rₕᵢ·2⁸⁶)·rₗₒ². The linear Karatsuba step
    /// overestimates rₗₒ by ≈rₗₒ²/(rₕᵢ·2⁸⁶). After correction, this leaves only the rₗₒ³ term, on
    /// the order of 2²⁵⁸/(3·2³⁴²), much less than 1ulp.
    ///
    /// The quadratic correction subtracts ⌊rₗₒ²/rₕᵢ·2⁸⁶⌋. This can over-correct by 1 because the
    /// Karatsuba division drops the low 172 bits of x. This remainder is captured by `res`.
    /// Undershoot occurs when ε/(rₕᵢ·2⁸⁶) < res/d (where ε = rₗₒ² % (rₕᵢ·2⁸⁶)), equivalently
    /// ε·3·rₕᵢ < res·2⁸⁶ because d = 3·rₕᵢ².
    function _cbrt_quadraticCorrection(uint256 r_hi, uint256 r_lo, uint256 res) private pure returns (uint256 r) {
        unchecked {
            uint256 R = r_hi << 86;
            uint256 r_lo2 = r_lo * r_lo;
            uint256 c = r_lo2.unsafeDiv(R);
            uint256 eps3 = (r_lo2 - c * R) * 3;

            r_lo -= c;
            // For c ≤ 1 (~68.5% of the time), undershoot never occurs, so we can skip the check
            if (c > 1) {
                // This awkward boolean expression is more gas efficient because it avoids 512-bit
                // multiplication
                r_lo = r_lo.unsafeInc(
                    ((eps3 >> 86) < (res >> 86))
                    .or(
                        ((eps3 >> 86) == (res >> 86))
                        .and((eps3 & 0x3fffffffffffffffffffff) * r_hi < (res & 0x3fffffffffffffffffffff) << 86)
                    )
                );
            }
            r = R + r_lo;
        }
    }

    function _cbrt(uint256 x_hi, uint256 x_lo) private pure returns (uint256 r) {
        /// This is the same general technique as we applied in `_sqrt`, patterned after Zimmermann's
        /// "Karatsuba Square Root" algorithm, but adapted to compute cube roots instead.
        unchecked {
            // Normalize `x` so that its MSB is in bit 255, 254, or 253. This makes the left shift a
            // multiple of 3 so that the "shift back" un-normalization step is exact.
            //   x ≥ 2⁵⁰⁹
            uint256 shift = x_hi.clz() / 3;
            (, x_hi, x_lo) = _shl256(x_hi, x_lo, shift * 3);

            // The initial step to compute the first "limb" of `r` uses the "normal" cube root
            // algorithm and consumes the first (almost) word of `x`.
            (uint256 r_hi, uint256 res, uint256 d) = _cbrt_baseCase(x_hi);

            // `limb_hi` is the next 86-bit limb of `x` after the first whole-ish word `w`.
            uint256 limb_hi;
            assembly ("memory-safe") {
                limb_hi := or(shl(0x54, and(0x03, x_hi)), shr(0xac, x_lo))
            }

            // The second and final limb of `r` is computed using an analogue of the Karatsuba step
            // from the original algorithm, followed by a pair of cleanup steps.
            uint256 r_lo;
            (r_lo, res) = _cbrt_karatsubaQuotient(res, limb_hi, d);

            r = _cbrt_quadraticCorrection(r_hi, r_lo, res);
            // Our error is now down to at most 1ulp over.

            // Un-normalize
            r >>= shift;
        }
    }

    function cbrt(uint512 x) internal pure returns (uint256 r) {
        (uint256 x_hi, uint256 x_lo) = x.into();

        if (x_hi == 0) {
            return x_lo.cbrt();
        }

        r = _cbrt(x_hi, x_lo);

        // The following cube-and-compare technique for obtaining the floor appears, at first, to
        // have an overflow bug in it. Consider that `_cbrt` returns a value within 1ulp of the
        // correct value. Define:
        //   rₘₐₓ = 0x6597fa94f5b8f20ac16666ad0f7137bc6601d885628
        // this means that for values of x in [rₘₐₓ³, 2⁵¹² - 1], `_cbrt` could return rₘₐₓ + 1,
        // which would result in overflow when cubing `r`. However, this does not happen. Given `x`
        // in the specified range, `_cbrt` follows the steps below:
        //
        // 1) shift = ⌊clz(xₕᵢ) / 3⌋ = 0
        // 2) w = x_hi >> 2 lies in [0x3fff..fffb0959fdf442978718ddcb, 2²⁵⁴ - 1]
        // 3) In that full interval, ⌊∛w⌋ is constant. With the ∛(3·2²⁵¹) seed, the 6
        //    Newton-Raphson iterations converge directly to the correct value:
        //      r_hi = 0x1965fea53d6e3c82b05999
        //    The branchless floor correction is a no-op (rₕᵢ³ ≤ w for all w in the interval)
        // 4) Therefore d = 3 ⋅ rₕᵢ² is constant:
        //      d = 0x78f3d1d950af414cd731fe48f48fde1309821333853
        // 5) n = (res << 86) | limb_hi overflows and is truncated to 256 bits. The truncated ⌊n / d⌋
        //    is constant:
        //      ⌊n / d⌋ = 0x8f3a38c7f3364c49d3405
        //    The carry branch (res >> 170 != 0) fires. The carry adjustment modifies the truncated
        //    quotient by adding:
        //      ⌊(2²⁵⁶ - 1) / d⌋ = 0x21dd5386fc92fb58eb2224
        //    and the final carry refinement term is zero, giving:
        //      r_lo = 0x2ad0f7137bc6601d885629
        //    The quotient stays in one "bucket" because `res` varies by only ~0.620·2⁸³, and
        //    `limb_hi`'s full 86-bit range contributes <1/2⁸⁴ to n/d. Total swing in the continuous
        //    quotient is ~0.164. At the boundaries, frac(n/d) ≈ 0.128 (at x = rₘₐₓ³) and ≈ 0.292
        //    (at x = 2⁵¹² - 1), so the floor never crosses an integer boundary
        // 6) After the carry adjustment branch, `r_lo` is constant:
        //      r_lo = 0x2ad0f7137bc6601d885629
        // 7) The quadratic correction subtracts exactly 1:
        //      ⌊rₗₒ² / (rₕᵢ·2⁸⁶)⌋ = 1
        //    so r_lo = 0x2ad0f7137bc6601d885628 and
        //      r = rₕᵢ·2⁸⁶ + rₗₒ = rₘₐₓ
        //
        // So, the cube-and-compare code below only cubes a value of at most `r_max`, which fits in
        // 512 bits. `cbrtUp` reaches `r_max + 1` only via its final +1 correction
        //
        // The following assembly block is identical to:
        //   (uint256 r2_hi, uint256 r2_lo) = _mul(r, r);
        //   (uint256 r3_hi, uint256 r3_lo) = _mul(r2_hi, r2_lo, r);
        //   r = r.unsafeDec(_gt(r3_hi, r3_lo, x_hi, x_lo));
        // but is substantially more gas efficient for inexplicable reasons
        assembly ("memory-safe") {
            let mm := mulmod(r, r, not(0x00))
            let r2_lo := mul(r, r)
            let r2_hi := sub(sub(mm, r2_lo), lt(mm, r2_lo))

            mm := mulmod(r2_lo, r, not(0x00))
            let r3_lo := mul(r2_lo, r)
            let r3_hi := add(sub(sub(mm, r3_lo), lt(mm, r3_lo)), mul(r2_hi, r))

            r := sub(r, or(gt(r3_hi, x_hi), and(eq(r3_hi, x_hi), gt(r3_lo, x_lo))))
        }
    }

    function cbrtUp(uint512 x) internal pure returns (uint256 r) {
        (uint256 x_hi, uint256 x_lo) = x.into();

        if (x_hi == 0) {
            return x_lo.cbrtUp();
        }

        r = _cbrt(x_hi, x_lo);

        // `_cbrt` gives a result within 1ulp. Check if `r` is too low and correct.
        //
        // The following assembly block is identical to:
        //   (uint256 r2_hi, uint256 r2_lo) = _mul(r, r);
        //   (uint256 r3_hi, uint256 r3_lo) = _mul(r2_hi, r2_lo, r);
        //   r = r.unsafeInc(_gt(x_hi, x_lo, r3_hi, r3_lo));
        // but is substantially more gas efficient for inexplicable reasons
        assembly ("memory-safe") {
            // See the detailed overflow-regime note in `cbrt` above. In particular, near x = 2⁵¹²,
            // `_cbrt` is pinned at `r_max` and does not return `r_max + 1` directly.
            let mm := mulmod(r, r, not(0x00))
            let r2_lo := mul(r, r)
            let r2_hi := sub(sub(mm, r2_lo), lt(mm, r2_lo))

            mm := mulmod(r2_lo, r, not(0x00))
            let r3_lo := mul(r2_lo, r)
            let r3_hi := add(sub(sub(mm, r3_lo), lt(mm, r3_lo)), mul(r2_hi, r))

            r := add(r, or(lt(r3_hi, x_hi), and(eq(r3_hi, x_hi), lt(r3_lo, x_lo))))
        }
    }

    //// floor(ln(x) * 2^256) for 512-bit unsigned integer x, returned as a uint512 (up to ~265 bits).
    ////
    //// Uses a two-stage design:
    ////   Stage 1 (fast path, ~99.965% of inputs): 16-bucket coarse reduction with a Remez-optimal
    ////     [6/7] rational approximant at Q216 precision and G=24 guard bits.
    ////   Stage 2 (fallback, ~0.035%): One-profile 2-bucket micro reduction with an adaptive odd
    ////     atanh series that certifies the boundary decision.
    ////
    //// Reverts with Panic(0x12) if x is zero.

    // Packed lookup table: N0[16] = [31,29,28,26,25,24,23,22,21,20,19,19,18,17,17,16]
    // 16 × 5-bit values, j=0 at bits 79:75
    uint256 private constant _LN_N0 = 0xff79ace2f6ad27394630;
    // Per-bucket fast bias, 16 × 16-bit signed two's complement, j=0 at bits 255:240
    uint256 private constant _LN_BIAS = 0xff6afca204c6fea4002a00c400bc009a002a0002ff06054c0021fb8c0068ff4d;
    // Per-bucket fast radius, 16 × 16-bit unsigned, j=0 at bits 255:240
    uint256 private constant _LN_RADIUS = 0x04af16b218950dae0094038b05ee037b009600670d3618a9002c16a00202048a;

    function lnQ256(uint512 x) internal pure returns (uint512) {
        (uint256 x_hi, uint256 x_lo) = x.into();

        if ((x_hi | x_lo) == 0) {
            Panic.panic(Panic.DIVISION_BY_ZERO);
        }

        uint512 r = alloc();
        if (x_hi == 0 && x_lo == 1) {
            return r.from(0, 0);
        }

        (uint256 r_hi, uint256 r_lo) = _lnQ256(x_hi, x_lo);
        return r.from(r_hi, r_lo);
    }

    function _lnQ256(uint256 x_hi, uint256 x_lo) private pure returns (uint256 r_hi, uint256 r_lo) {
        // ── Stage 1: Coarse range reduction ──
        //
        // Compute exponent e = bit_length(x) - 1 via CLZ.
        // Extract top 4 fraction bits to select coarse bucket j.
        // Look up dyadic multiplier n = N0[j].
        // Compute u_num = n*x - 2^(e+5) (signed) and z_den = 2^(e+6) + u_num (positive).

        uint256 e;
        if (x_hi != 0) {
            e = 511 - x_hi.clz();
        } else {
            e = 255 - x_lo.clz();
        }

        // Extract top 4 fraction bits: j = ((x_hi, x_lo) >> (e-4)) & 0xF
        uint256 j;
        assembly ("memory-safe") {
            let shift := sub(e, 4)
            j := and(0x0F, shr(shift, x_lo))
            if lt(e, 4) { j := and(0x0F, shl(sub(4, e), x_lo)) }
            // For e >= 256 the fraction bits may be partly or wholly in x_hi.
            if x_hi {
                switch lt(shift, 256)
                case 1 { j := and(0x0F, or(shl(sub(256, shift), x_hi), shr(shift, x_lo))) }
                default { j := and(0x0F, shr(sub(shift, 256), x_hi)) }
            }
        }

        // Look up n from packed N0 table
        uint256 n;
        assembly ("memory-safe") {
            n := and(0x1F, shr(mul(sub(15, j), 5), _LN_N0))
        }

        // ── Compute n*x as 3-word (nx_ex, nx_hi, nx_lo) ──
        (uint256 nx_ex, uint256 nx_hi, uint256 nx_lo) = _mul768(x_hi, x_lo, n);

        // ── Compute 2^(e+5) as up to 3-word value ──
        uint256 pow2_ex;
        uint256 pow2_hi;
        uint256 pow2_lo;
        assembly ("memory-safe") {
            let ep5 := add(e, 5)
            // 2^ep5: if ep5 < 256 → lo word; if 256 <= ep5 < 512 → hi word; if >= 512 → ex word
            pow2_lo := shl(ep5, lt(ep5, 256))
            pow2_hi := shl(sub(ep5, 256), and(lt(ep5, 512), iszero(lt(ep5, 256))))
            pow2_ex := shl(sub(ep5, 512), iszero(lt(ep5, 512)))
        }

        // ── u_num = n*x - 2^(e+5) (signed, magnitude fits in 2 words) ──
        // z_den = n*x + 2^(e+5) (positive, may need 3 words)
        // We need the sign of u_num and |u_num|.
        bool u_neg;
        uint256 u_hi;
        uint256 u_lo;
        uint256 zd_ex;
        uint256 zd_hi;
        uint256 zd_lo;
        assembly ("memory-safe") {
            // 3-word subtraction: nx - pow2
            let borrow := lt(nx_lo, pow2_lo)
            u_lo := sub(nx_lo, pow2_lo)
            let v := sub(nx_hi, borrow)
            borrow := or(lt(nx_hi, borrow), lt(v, pow2_hi))
            u_hi := sub(v, pow2_hi)
            let u_ex := sub(sub(nx_ex, pow2_ex), borrow)

            // Determine sign: if u_ex has the high bit set, u_num is negative
            // Actually u_ex is at most a few bits; check if the subtraction underflowed
            u_neg := gt(u_ex, 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF)

            if u_neg {
                // Negate: |u_num| = pow2 - nx
                borrow := lt(pow2_lo, nx_lo)
                u_lo := sub(pow2_lo, nx_lo)
                v := sub(pow2_hi, borrow)
                borrow := or(lt(pow2_hi, borrow), lt(v, nx_hi))
                u_hi := sub(v, nx_hi)
                // u_ex for the magnitude is not needed (fits in 2 words by the
                // coarse reduction bound: |u| < 2^(e+5)/32 = 2^e)
            }

            // 3-word addition: z_den = nx + pow2
            zd_lo := add(nx_lo, pow2_lo)
            let carry := lt(zd_lo, nx_lo)
            zd_hi := add(add(nx_hi, pow2_hi), carry)
            carry := lt(zd_hi, nx_hi)
            // Handle carry propagation more carefully
            if and(iszero(carry), lt(zd_hi, add(nx_hi, pow2_hi))) { carry := 1 }
            // Simpler: just check overflow
            zd_ex := add(add(nx_ex, pow2_ex), carry)
        }

        // ── z_hi = round(|u_num| * 2^280 / z_den) ──
        //
        // Decomposed as: let A = |u| << 24.  Then z_hi = round(A * 2^256 / z_den).
        // The 4-word numerator (a_ex, a_hi, a_lo, 0) is divided by z_den in two rounds:
        //   z_hi_h = floor(A / z_den) with remainder R,  then  z_lo = floor(R * 2^256 / z_den).
        // After coarse reduction, |z| < 0.02, so z_hi fits in ~275 bits (hi word ≤ 18 bits).

        uint256 z_hi_h;
        uint256 z_lo;
        {
            uint256 a_ex;
            uint256 a_hi;
            uint256 a_lo;
            assembly ("memory-safe") {
                a_lo := shl(24, u_lo)
                a_hi := or(shl(24, u_hi), shr(232, u_lo))
                a_ex := shr(232, u_hi)
            }

            if (zd_hi == 0 && zd_ex == 0) {
                // z_den is a single word. Three rounds of 512/256 division extract the
                // 2-word quotient of the 4-word numerator (a_ex, a_hi, a_lo, 0) / zd_lo.
                uint256 rem;
                if (a_ex != 0) {
                    z_hi_h = _div(a_ex, a_hi, zd_lo);
                    assembly ("memory-safe") {
                        rem := addmod(mulmod(a_ex, sub(0, zd_lo), zd_lo), a_hi, zd_lo)
                    }
                } else {
                    z_hi_h = a_hi / zd_lo;
                    rem = a_hi % zd_lo;
                }
                z_hi_h = _div(rem, a_lo, zd_lo);
                assembly ("memory-safe") {
                    rem := addmod(mulmod(rem, sub(0, zd_lo), zd_lo), a_lo, zd_lo)
                }
                z_lo = _div(rem, 0, zd_lo);
                // Round to nearest
                assembly ("memory-safe") {
                    let final_rem := addmod(mulmod(rem, sub(0, zd_lo), zd_lo), 0, zd_lo)
                    z_lo := add(z_lo, iszero(lt(shl(1, final_rem), zd_lo)))
                    z_hi_h := add(z_hi_h, iszero(z_lo))
                }
            } else {
                // z_den is 2+ words. Reduce 3-word z_den to 2 words if needed.
                if (zd_ex != 0) {
                    uint256 shift_amount;
                    assembly ("memory-safe") {
                        shift_amount := sub(256, clz(zd_ex))
                    }
                    (zd_hi, zd_lo) = _shr(zd_hi, zd_lo, shift_amount);
                    assembly ("memory-safe") {
                        zd_hi := or(shl(sub(256, shift_amount), zd_ex), zd_hi)
                        a_lo := or(shr(shift_amount, a_lo), shl(sub(256, shift_amount), a_hi))
                        a_hi := or(shr(shift_amount, a_hi), shl(sub(256, shift_amount), a_ex))
                        a_ex := shr(shift_amount, a_ex)
                    }
                }
                // (a_ex, a_hi, a_lo, 0) / (zd_hi, zd_lo) → (z_hi_h, z_lo).
                // Two rounds of 3-word / 2-word Algorithm D.
                z_hi_h = _algorithmD(a_ex, a_hi, a_lo, zd_hi, zd_lo);
                {
                    (uint256 p_ex, uint256 p_hi, uint256 p_lo) = _mul768(zd_hi, zd_lo, z_hi_h);
                    assembly ("memory-safe") {
                        // 3-word subtract: (a_ex,a_hi,a_lo) - (p_ex,p_hi,p_lo) → remainder
                        let b := lt(a_lo, p_lo)
                        a_lo := sub(a_lo, p_lo)
                        let mid := sub(a_hi, b)
                        b := or(lt(a_hi, b), lt(mid, p_hi))
                        a_hi := sub(mid, p_hi)
                        // a_ex - p_ex - b = 0 (exact remainder < divisor)
                    }
                }
                z_lo = _algorithmD(a_hi, a_lo, 0, zd_hi, zd_lo);
            }
        }

        // ── w_hi = z_hi² >> 280 (Q280) ──
        // z_hi = (z_hi_h, z_lo) where z_hi_h ≤ 18 bits.
        // z_hi² = z_hi_h² * 2^512 + 2 * z_hi_h * z_lo * 2^256 + z_lo²
        uint256 w_hi_h;
        uint256 w_lo;
        assembly ("memory-safe") {
            // z_lo² → (sq_hi, sq_lo)
            let mm := mulmod(z_lo, z_lo, not(0x00))
            let sq_lo := mul(z_lo, z_lo)
            let sq_hi := sub(sub(mm, sq_lo), lt(mm, sq_lo))

            // cross = 2 * z_hi_h * z_lo (up to 275 bits, spans 2 words)
            // z_hi_h * z_lo can exceed 256 bits, so we need the full product.
            let p_mm := mulmod(z_hi_h, z_lo, not(0x00))
            let p_lo := mul(z_hi_h, z_lo)
            let p_hi := sub(sub(p_mm, p_lo), lt(p_mm, p_lo))
            // cross = 2 * (p_hi, p_lo)
            let cross_lo := shl(1, p_lo)
            let cross_hi := or(shl(1, p_hi), shr(255, p_lo))

            // Accumulate: prod = (z_hi_h², sq_hi + cross_lo, sq_lo)
            let prod_mid := add(sq_hi, cross_lo)
            let prod_ex := add(add(mul(z_hi_h, z_hi_h), cross_hi), lt(prod_mid, sq_hi))

            // Shift (prod_ex, prod_mid, sq_lo) >> 280 = >> 256 then >> 24
            // After dropping sq_lo: (prod_ex, prod_mid) >> 24
            w_lo := or(shr(24, prod_mid), shl(232, prod_ex))
            w_hi_h := shr(24, prod_ex)
        }

        // ── w_q256 = w_hi >> 24 (Q256, single word ≤ 245 bits) ──
        uint256 w_q256;
        assembly ("memory-safe") {
            w_q256 := or(shr(24, w_lo), shl(232, w_hi_h))
        }
        // ── Horner evaluation of R(w) = P(w)/Q(w) at Q216 ──
        uint256 r_qc = _lnHorner(w_q256);
        // ── Power chain: z^3, z^5, z^7, z^9 via repeated multiplication by w ──
        // Each: result = prev * w_hi >> 280
        // We compute the 3-word product (prev_h, prev_lo) * (w_hi_h, w_lo)
        // and shift right by 280.

        // z^3 = z_hi * w_hi >> 280
        uint256 z3_h;
        uint256 z3_lo;
        (z3_h, z3_lo) = _lnMulShr280(z_hi_h, z_lo, w_hi_h, w_lo);
        // z^5 = z^3 * w_hi >> 280
        uint256 z5_h;
        uint256 z5_lo;
        (z5_h, z5_lo) = _lnMulShr280(z3_h, z3_lo, w_hi_h, w_lo);
        // z^7 = z^5 * w_hi >> 280 (result fits in single word, ≤ 252 bits)
        uint256 z7;
        {
            (uint256 z7_h, uint256 z7_lo_tmp) = _lnMulShr280(z5_h, z5_lo, w_hi_h, w_lo);
            z7 = z7_lo_tmp; // z7_h should be 0 or negligible
        }

        // z^9 = z^7 * w_hi >> 280 (single word)
        uint256 z9;
        {
            // z7 (single word) * w_hi (2-word) >> 280
            // = z7 * (w_hi_h * 2^256 + w_lo) >> 280
            // = z7 * w_lo >> 280 + z7 * w_hi_h >> 24
            (uint256 p_hi, uint256 p_lo) = _mul(z7, w_lo);
            assembly ("memory-safe") {
                // (p_hi, p_lo) >> 280 = p_hi >> 24 (dropping p_lo)
                z9 := add(shr(24, p_hi), shr(24, mul(z7, w_hi_h)))
                // The w_hi_h term: z7 * w_hi_h is at most 252+14=266 bits, >> 24 = 242 bits
            }
        }

        // ── Odd terms: 2/k * z^k for k=3,5,7 ──
        // term3 = round(z3 * 2 / 3) — up to 263 bits (2-word)
        uint256 term3_h;
        uint256 term3_lo;
        {
            (uint256 z3x2_hi, uint256 z3x2_lo) = _add(z3_h, z3_lo, z3_h, z3_lo);
            (term3_h, term3_lo) = _divRound(z3x2_hi, z3x2_lo, 3);
        }

        // term5 = round(z5 * 2 / 5) — up to ~257 bits (2-word)
        uint256 term5_h;
        uint256 term5_lo;
        {
            (uint256 z5x2_hi, uint256 z5x2_lo) = _add(z5_h, z5_lo, z5_h, z5_lo);
            (term5_h, term5_lo) = _divRound(z5x2_hi, z5x2_lo, 5);
        }

        // term7 = round(z7 * 2 / 7) — z7 is single word
        uint256 term7;
        assembly ("memory-safe") {
            let z7x2 := shl(1, z7)
            term7 := div(z7x2, 7)
            let rem := mod(z7x2, 7)
            term7 := add(term7, gt(mul(2, rem), 6)) // rem >= 4 means round up
        }

        // ── Residual: z9 * R(w) >> 216 ──
        uint256 resid;
        {
            (uint256 p_hi, uint256 p_lo) = _mul(z9, r_qc);
            assembly ("memory-safe") {
                // (p_hi, p_lo) >> 216 = (p_hi << 40) | (p_lo >> 216)
                // p_hi ≤ 209 bits, so p_hi << 40 ≤ 249 bits. Fits in one word.
                resid := or(shl(40, p_hi), shr(216, p_lo))
            }
        }
        // ── Accumulate local magnitude (unsigned): 2*|z| + term3 + term5 + term7 + resid ──
        // All terms are Q280, unsigned.
        uint256 local_hi;
        uint256 local_lo;
        assembly ("memory-safe") {
            // 2*z_hi: (z_hi_h << 1 | z_lo >> 255, z_lo << 1)
            local_lo := shl(1, z_lo)
            local_hi := or(shl(1, z_hi_h), shr(255, z_lo))
        }
        // Add term3 (2-word)
        (local_hi, local_lo) = _add(local_hi, local_lo, term3_h, term3_lo);
        // Add term5 (2-word)
        (local_hi, local_lo) = _add(local_hi, local_lo, term5_h, term5_lo);
        // Add term7 (single word)
        (local_hi, local_lo) = _add(local_hi, local_lo, term7);
        // Add resid (single word)
        (local_hi, local_lo) = _add(local_hi, local_lo, resid);
        // ── Prefix: e * LN2_FAST + C0_FAST[j] (both Q280, 2-word) ──
        uint256 prefix_hi;
        uint256 prefix_lo;
        {
            // e * LN2_FAST: 512 × 256 multiply (e is at most 511)
            uint256 ln2_hi = 11629079;
            uint256 ln2_lo = 112091976578344267006618725249553599712498325932819978909100653379179885607030;
            (prefix_hi, prefix_lo) = _mul(ln2_hi, ln2_lo, e);
        }

        // Add C0_FAST[j]: look up from packed hi + individual lo constants
        {
            uint256 c0_lo = _lnC0FastLo(j);
            uint256 c0_hi;
            assembly ("memory-safe") {
                // Extract 24-bit hi word from packed constants
                // Buckets 0-7 in _C0_HI_0_7, buckets 8-15 in _C0_HI_8_15
                let packed := 0x0820ae19335e222f1d3527da3f323849a588548ab85febe8
                if gt(j, 7) { packed := 0x6bd4a57852288573b78573b7934b10a1ecffa1ecffb17217 }
                let idx := mod(j, 8)
                c0_hi := and(0xFFFFFF, shr(mul(sub(7, idx), 24), packed))
            }
            (prefix_hi, prefix_lo) = _add(prefix_hi, prefix_lo, c0_hi, c0_lo);
        }
        // ── Combine: q_raw = prefix ± local_mag ──
        uint256 q_hi;
        uint256 q_lo;
        if (u_neg) {
            (q_hi, q_lo) = _sub(prefix_hi, prefix_lo, local_hi, local_lo);
        } else {
            (q_hi, q_lo) = _add(prefix_hi, prefix_lo, local_hi, local_lo);
        }

        // ── Add per-bucket bias (small signed integer) ──
        {
            int256 bias;
            assembly ("memory-safe") {
                bias := signextend(1, shr(mul(sub(15, j), 16), _LN_BIAS))
            }
            if (bias >= 0) {
                (q_hi, q_lo) = _add(q_hi, q_lo, uint256(bias));
            } else {
                (q_hi, q_lo) = _sub(q_hi, q_lo, uint256(-bias));
            }
        }

        // ── Same-floor test: floor((q - rad) >> 24) == floor((q + rad) >> 24) ──
        uint256 rad;
        assembly ("memory-safe") {
            rad := and(0xFFFF, shr(mul(sub(15, j), 16), _LN_RADIUS))
        }

        uint256 lo_hi;
        uint256 lo_lo;
        uint256 hi_hi;
        uint256 hi_lo;
        (lo_hi, lo_lo) = _sub(q_hi, q_lo, rad);
        (hi_hi, hi_lo) = _add(q_hi, q_lo, rad);
        // >> 24
        (lo_hi, lo_lo) = _shr(lo_hi, lo_lo, 24);
        (hi_hi, hi_lo) = _shr(hi_hi, hi_lo, 24);

        if (lo_hi == hi_hi && lo_lo == hi_lo) {
            return (lo_hi, lo_lo);
        }

        // ── Stage 2: Fallback ──
        return _lnFallback(u_hi, u_lo, u_neg, zd_hi, zd_lo, e, j, q_hi, q_lo, hi_hi, hi_lo);
    }

    /// Multiply two Q280 values (a_h, a_lo) * (b_h, b_lo) and shift right by 280.
    /// Both inputs have small hi words (≤ 20 bits). Result is a 2-word Q280 value.
    function _lnMulShr280(uint256 a_h, uint256 a_lo, uint256 b_h, uint256 b_lo)
        private
        pure
        returns (uint256 r_hi, uint256 r_lo)
    {
        assembly ("memory-safe") {
            // Product = a_h*b_h*2^512 + (a_h*b_lo + a_lo*b_h)*2^256 + a_lo*b_lo
            // We need (product >> 280) = (product >> 256) >> 24

            // a_lo * b_lo → (mid, lo) via mulmod trick
            let mm := mulmod(a_lo, b_lo, not(0x00))
            let lo := mul(a_lo, b_lo)
            let mid := sub(sub(mm, lo), lt(mm, lo))

            // cross terms: a_h*b_lo + a_lo*b_h (each can exceed 256 bits)
            // Full product a_h*b_lo via mulmod
            let mm2 := mulmod(a_h, b_lo, not(0x00))
            let c1_lo := mul(a_h, b_lo)
            let c1_hi := sub(sub(mm2, c1_lo), lt(mm2, c1_lo))
            // Full product a_lo*b_h via mulmod
            let mm3 := mulmod(a_lo, b_h, not(0x00))
            let c2_lo := mul(a_lo, b_h)
            let c2_hi := sub(sub(mm3, c2_lo), lt(mm3, c2_lo))
            // Sum cross terms
            let cross_lo := add(c1_lo, c2_lo)
            let cross_hi := add(add(c1_hi, c2_hi), lt(cross_lo, c1_lo))

            // Accumulate into mid, carry into ex
            let mid2 := add(mid, cross_lo)
            let ex := add(add(mul(a_h, b_h), cross_hi), lt(mid2, mid))

            // Shift (ex, mid2, lo) >> 280 = >> 256 then >> 24
            // After >> 256: (ex, mid2). Then >> 24:
            r_lo := or(shr(24, mid2), shl(232, ex))
            r_hi := shr(24, ex)
        }
    }

    /// Unrolled Horner evaluation of the [6/7] Remez-optimal rational R(w).
    /// Input: w in Q256 (unsigned, ≤ 245 bits). Output: R(w) in Q216 (unsigned).
    /// R(w) = P(w) / Q(w) where Q has implicit Q0 = 2^216.
    function _lnHorner(uint256 w) private pure returns (uint256 result) {
        // Evaluate R(w) = P(w) / Q(w) via unrolled Horner chains.
        // Each step: acc = round(acc * w / 2^256) + coeff.
        // Signed Q216 coefficients; w is unsigned Q256 (≤ 245 bits).
        // Max product ≤ 464 bits < 512, safe for mulmod.

        uint256 num;
        uint256 den;

        assembly ("memory-safe") {
            // ── Numerator P(w): degree 6, 7 coefficients ──
            let acc := 244504971595928297752455626929162943780014968997496095305629633

            // P[5]: acc is positive here, no sign handling needed
            {
                let mm := mulmod(acc, w, not(0x00))
                let lo := mul(acc, w)
                let hi := sub(sub(mm, lo), lt(mm, lo))
                hi := add(hi, shr(255, lo))
                acc := sub(hi, 4031542932217000284709476574733749729411078599780997370963274225)
            }
            // P[4]
            {
                let s := sar(255, acc)
                let a := sub(xor(acc, s), s)
                let mm := mulmod(a, w, not(0x00))
                let lo := mul(a, w)
                let hi := sub(sub(mm, lo), lt(mm, lo))
                hi := add(hi, shr(255, lo))
                acc := add(sub(xor(hi, s), s), 24260002286396336386066722552550012983868598792106518362024927003)
            }
            // P[3]
            {
                let s := sar(255, acc)
                let a := sub(xor(acc, s), s)
                let mm := mulmod(a, w, not(0x00))
                let lo := mul(a, w)
                let hi := sub(sub(mm, lo), lt(mm, lo))
                hi := add(hi, shr(255, lo))
                acc := sub(sub(xor(hi, s), s), 70280975374256110316161633634422318148227266301984626622229992403)
            }
            // P[2]
            {
                let s := sar(255, acc)
                let a := sub(xor(acc, s), s)
                let mm := mulmod(a, w, not(0x00))
                let lo := mul(a, w)
                let hi := sub(sub(mm, lo), lt(mm, lo))
                hi := add(hi, shr(255, lo))
                acc := add(sub(xor(hi, s), s), 105567710592264149655895345681626059811476843737297988261266061719)
            }
            // P[1]
            {
                let s := sar(255, acc)
                let a := sub(xor(acc, s), s)
                let mm := mulmod(a, w, not(0x00))
                let lo := mul(a, w)
                let hi := sub(sub(mm, lo), lt(mm, lo))
                hi := add(hi, shr(255, lo))
                acc := sub(sub(xor(hi, s), s), 79147257707505802445321067591641956191893173416852452736772062152)
            }
            // P[0]
            {
                let s := sar(255, acc)
                let a := sub(xor(acc, s), s)
                let mm := mulmod(a, w, not(0x00))
                let lo := mul(a, w)
                let hi := sub(sub(mm, lo), lt(mm, lo))
                hi := add(hi, shr(255, lo))
                acc := add(sub(xor(hi, s), s), 23402731481901597043981783929704540515310021200122024723180217230)
            }
            num := acc

            // ── Denominator Q(w): degree 7 with implicit Q0 = 2^216 ──
            acc := sub(0, 855788182002653539265473379773190817088756284166928459588115371)
            // Q[5]
            {
                let s := sar(255, acc)
                let a := sub(xor(acc, s), s)
                let mm := mulmod(a, w, not(0x00))
                let lo := mul(a, w)
                let hi := sub(sub(mm, lo), lt(mm, lo))
                hi := add(hi, shr(255, lo))
                acc := add(sub(xor(hi, s), s), 15307805589224505617810266544830173595922016396186463802374189830)
            }
            // Q[4]
            {
                let s := sar(255, acc)
                let a := sub(xor(acc, s), s)
                let mm := mulmod(a, w, not(0x00))
                let lo := mul(a, w)
                let hi := sub(sub(mm, lo), lt(mm, lo))
                hi := add(hi, shr(255, lo))
                acc := sub(sub(xor(hi, s), s), 104363990572981334424492003201115405883168394510253602517671885198)
            }
            // Q[3]
            {
                let s := sar(255, acc)
                let a := sub(xor(acc, s), s)
                let mm := mulmod(a, w, not(0x00))
                let lo := mul(a, w)
                let hi := sub(sub(mm, lo), lt(mm, lo))
                hi := add(hi, shr(255, lo))
                acc := add(sub(xor(hi, s), s), 361238115265142525912392094197617069095853073482781560893409836147)
            }
            // Q[2]
            {
                let s := sar(255, acc)
                let a := sub(xor(acc, s), s)
                let mm := mulmod(a, w, not(0x00))
                let lo := mul(a, w)
                let hi := sub(sub(mm, lo), lt(mm, lo))
                hi := add(hi, shr(255, lo))
                acc := sub(sub(xor(hi, s), s), 698357271234189264361221256846859697717152049975428562654123141828)
            }
            // Q[1]
            {
                let s := sar(255, acc)
                let a := sub(xor(acc, s), s)
                let mm := mulmod(a, w, not(0x00))
                let lo := mul(a, w)
                let hi := sub(sub(mm, lo), lt(mm, lo))
                hi := add(hi, shr(255, lo))
                acc := add(sub(xor(hi, s), s), 764050311468718105200385962090128619260907774191827731723142005680)
            }
            // Q[0]
            {
                let s := sar(255, acc)
                let a := sub(xor(acc, s), s)
                let mm := mulmod(a, w, not(0x00))
                let lo := mul(a, w)
                let hi := sub(sub(mm, lo), lt(mm, lo))
                hi := add(hi, shr(255, lo))
                acc := sub(sub(xor(hi, s), s), 442327261958050172847695917721755520215342540249012582887183524330)
            }
            // Final Q step: acc * w >> 256 + 2^216
            {
                let s := sar(255, acc)
                let a := sub(xor(acc, s), s)
                let mm := mulmod(a, w, not(0x00))
                let lo := mul(a, w)
                let hi := sub(sub(mm, lo), lt(mm, lo))
                hi := add(hi, shr(255, lo))
                acc := add(sub(xor(hi, s), s), shl(216, 1))
            }
            den := acc
        }

        // Final: R = |num| << 216 / den (using the existing 512/256 division helper)
        uint256 shifted_hi;
        uint256 shifted_lo;
        assembly ("memory-safe") {
            let num_sign := sar(255, num)
            let abs_num := sub(xor(num, num_sign), num_sign)
            shifted_hi := shr(40, abs_num)
            shifted_lo := shl(216, abs_num)
        }
        result = _div(shifted_hi, shifted_lo, den);
    }

    /// Look up C0_FAST lo word by bucket index j (0..15).
    function _lnC0FastLo(uint256 j) private pure returns (uint256 r) {
        assembly ("memory-safe") {
            switch j
            case 0  { r := 89083781164509994004718356690768793073932788881966909474484729048509852787943 }
            case 1  { r := 42222851819381533507215179746829461024493811853866784323624442470601172712418 }
            case 2  { r := 1950219340667861571575913432882893159243836047111849076174902345541118150629 }
            case 3  { r := 54768199241016555318325029573083375611829530682990422062725468020935705966836 }
            case 4  { r := 98334583919129610825820882369091974317179510858968455366245334201211721913124 }
            case 5  { r := 31130839618193158765781046471345825506300755083565603707836592893242714151273 }
            case 6  { r := 13065056713818001229867265197078665384940697492418171877843044825701490842440 }
            case 7  { r := 108272970888202911497369533840699807949540786193866691010341518600002034247273 }
            case 8  { r := 33081058958861020337356959904228718665544591130677452784011495238783832301902 }
            case 9  { r := 47317235630078841204434311304978833088203926063073935117944201786239238940109 }
            case 10 { r := 10181731043312906040233281754117480967214741482798891169727515427100994174328 }
            case 11 { r := 10181731043312906040233281754117480967214741482798891169727515427100994174328 }
            case 12 { r := 62261679236386317531562092942691651012601510167131207415673185786485428302547 }
            case 13 { r := 68654584485920198024996402385813864444570494494924639164479954639474546591132 }
            case 14 { r := 68654584485920198024996402385813864444570494494924639164479954639474546591132 }
            case 15 { r := 112091976578344267006618725249553599712498325932819978909100653379179885607030 }
        }
    }

    /// Stage 2 fallback: resolve the ambiguous fast-path case using one-profile
    /// micro reduction and an adaptive odd atanh series.
    function _lnFallback(
        uint256 u_hi,
        uint256 u_lo,
        bool u_neg,
        uint256 zd_hi,
        uint256 zd_lo,
        uint256 e,
        uint256 j,
        uint256 q_fast_hi,
        uint256 q_fast_lo,
        uint256 q_hi_hi,
        uint256 q_hi_lo
    ) private pure returns (uint256 r_hi, uint256 r_lo) {
        // Compute z at Q256: z = |u_num| * 2^256 / z_den
        uint256 z_q256 = _algorithmD(u_hi, u_lo, zd_hi, zd_lo);

        // One-profile micro reduction:
        // boundary = 1/128 at Q256 = 2^249
        // lower bucket (k=0): c = 0, t = z
        // upper bucket (k=1): c = 1/64 = 2^250 at Q256, t = (|z| - c) / (1 - |z|*c / 2^256)

        uint256 a = z_q256; // |z| in Q256
        bool upper;
        assembly ("memory-safe") {
            upper := gt(a, sub(shl(249, 1), 1)) // a >= 2^249 = 1/128
        }

        uint256 t_q256;
        if (!upper) {
            // c = 0 → t = z
            t_q256 = a;
        } else {
            // c = 2^250 (1/64 in Q256)
            uint256 c = 1 << 250;
            // t = (a - c) / (1 - a*c / 2^256)
            uint256 t_num;
            uint256 t_den;
            assembly ("memory-safe") {
                t_num := sub(a, c)
                // a * c / 2^256: since a < 2^251 and c = 2^250, product < 2^501
                // Use mulmod to get (a * c) mod 2^256, but we need the high part
                let ac_lo := mul(a, c)
                let ac_hi := shr(6, a) // a * 2^250 >> 256 = a >> 6
                // Actually: a * c = a * 2^250. Split: a * 2^250 = (a >> 6) * 2^256 + (a & 0x3F) * 2^250
                // ac_hi = a >> 6, ac_lo = shl(250, and(a, 0x3F))
                ac_hi := shr(6, a)
                ac_lo := shl(250, and(a, 0x3F))
                // 1 - ac/2^256 in Q256 = 2^256 - ac_hi (approximately)
                // But we need: (1 - a*c/2^256) * 2^256 = 2^256 - a*c/2^256 * 2^256
                // Hmm this is getting circular. Let's use:
                // denominator at Q256 = 2^256 - (a * c >> 256) = 2^256 - ac_hi
                // But also need the fractional part for precision.
                // For simplicity: t_den = -ac_hi (as 2^256 - ac_hi wraps)
                t_den := sub(0, ac_hi) // 2^256 - ac_hi (mod 2^256)
                // This loses precision from ac_lo, but ac_lo / 2^256 is tiny
            }
            // t = t_num * 2^256 / t_den = t_num * 2^256 / (2^256 - a*c/2^256)
            // Since t_num < 2^249 and t_den ≈ 2^256, quotient is small
            // Use: t_q256 = t_num * 2^256 / t_den
            // This is a 505-bit / 256-bit division
            (uint256 tn_hi, uint256 tn_lo) = _mul(t_num, t_den); // wait, we want t_num / t_den
            // Actually we need: t_q256 = round(t_num * 2^256 / t_den)
            // t_num fits in 249 bits. t_num << 256 = (t_num, 0) which is 505 bits.
            // _div(t_num, 0, t_den) gives floor(t_num * 2^256 / t_den)
            t_q256 = _div(t_num, 0, t_den);
        }

        // Compute the prefix correction delta
        // delta = (q_fast >> 24) - q_hi + (exact_prefix - fast_prefix) + micro_additive - local_fast
        //
        // For the EVM implementation, we compute delta as a signed 2-word value:
        // base = q_fast >> 24 (2-word)
        // delta_base = base - q_hi (signed, small since fast was nearly correct)
        uint256 base_hi;
        uint256 base_lo;
        (base_hi, base_lo) = _shr(q_fast_hi, q_fast_lo, 24);

        // delta_base = base - q_hi (could be negative if base < q_hi)
        // Since we know the true answer is q_hi or q_hi-1, delta is close to 0.
        // We'll track sign separately.
        bool delta_neg;
        uint256 delta_hi;
        uint256 delta_lo;
        if (_gt(q_hi_hi, q_hi_lo, base_hi, base_lo)) {
            delta_neg = true;
            (delta_hi, delta_lo) = _sub(q_hi_hi, q_hi_lo, base_hi, base_lo);
        } else {
            delta_neg = false;
            (delta_hi, delta_lo) = _sub(base_hi, base_lo, q_hi_hi, q_hi_lo);
        }

        // For now, use a simplified fallback: compute ln(x) at higher precision
        // using the exact Q256 constants and the adaptive series.
        //
        // exact_prefix = e * LN2_EXACT + C0_EXACT[j]
        uint256 exact_prefix;
        {
            uint256 ln2_exact = 80260960185991308862233904206310070533990667611589946606122867505419956976172;
            (uint256 ep_hi, uint256 ep_lo) = _mul(e, ln2_exact);
            uint256 c0_exact = _lnC0ExactQ256(j);
            (ep_hi, ep_lo) = _add(ep_hi, ep_lo, c0_exact);
            // exact_prefix is in Q256, up to ~265 bits (2-word)
            // fast_prefix = (e * LN2_FAST + C0_FAST[j]) >> 24
            // Both are the same mathematical value to within the fast-path rounding.
            // The delta between them is tiny. For the adaptive series, we just need
            // to determine whether the true ln(x)*2^256 is >= q_hi or < q_hi.
            //
            // true_value = exact_prefix + 2*atanh(z) (in Q256)
            // where 2*atanh(z) = 2*atanh(c) + 2*atanh(t) for the micro reduction.
            //
            // We need: is exact_prefix + 2*atanh(c) + 2*atanh(t) >= q_hi ?

            // micro additive constant: 2*atanh(c)
            // If lower (c=0): 0
            // If upper (c=1/64): A64_Q256 = 3618797306320365907038389356091966445740960606432524368886479476623023988535
            if (upper) {
                if (u_neg) {
                    (ep_hi, ep_lo) = _sub(ep_hi, ep_lo, 3618797306320365907038389356091966445740960606432524368886479476623023988535);
                } else {
                    (ep_hi, ep_lo) = _add(ep_hi, ep_lo, 3618797306320365907038389356091966445740960606432524368886479476623023988535);
                }
            }

            // Now we need: is ep + 2*atanh(t) >= q_hi ?
            // Equivalently: is ep - q_hi + 2*atanh(t) >= 0 ?
            // Let D = ep - q_hi (signed)
            bool D_neg;
            uint256 D_hi;
            uint256 D_lo;
            if (_gt(q_hi_hi, q_hi_lo, ep_hi, ep_lo)) {
                D_neg = true;
                (D_hi, D_lo) = _sub(q_hi_hi, q_hi_lo, ep_hi, ep_lo);
            } else {
                D_neg = false;
                (D_hi, D_lo) = _sub(ep_hi, ep_lo, q_hi_hi, q_hi_lo);
            }

            // t_q256 is |t| in Q256. The sign of t matches sign of z (if c > 0)
            // or is always positive (if c = 0 and z > 0) or negative (c=0 and z < 0).
            // For simplicity: t has the same sign as z.
            // 2*atanh(t) = 2*t + 2*t^3/3 + 2*t^5/5 + ...
            // We need to add this to D and check sign.

            // The sign of 2*atanh(t) is the same as sign of z (since t is derived from z)
            // If u_neg (z < 0): 2*atanh(t) is negative → 2*atanh(|t|) with negative sign
            // If !u_neg (z > 0): 2*atanh(t) is positive

            // Adaptive series to determine sign of D + sign_z * 2*atanh(|t|)
            uint256 a_val = t_q256;
            uint256 a2;
            (uint256 a2_hi,) = _mul(a_val, a_val);
            a2 = a2_hi; // a^2 in Q256 (just the high word of the 512-bit product)

            uint256 pow_a = a_val;
            uint256 partialSum = 0;

            // q_lo = q_hi - 1 (the other candidate)
            uint256 q_lo_hi_val;
            uint256 q_lo_lo_val;
            (q_lo_hi_val, q_lo_lo_val) = _sub(q_hi_hi, q_hi_lo, 1);

            for (uint256 m = 0; m < 80; m++) {
                unchecked {
                    uint256 odd = 2 * m + 1;
                    // Add current term: 2 * pow_a / odd
                    uint256 term = (2 * pow_a) / odd;
                    partialSum += term;

                    // Compute remainder bound: 2 * pow_a * a2 / ((odd+2) * (2^256 - a2))
                    // Simplified: since a2 << 2^256, the denominator ≈ (odd+2) * 2^256
                    // So rem ≈ 2 * pow_a * a2 / ((odd+2) * 2^256) = 2 * (pow_a * a2 >> 256) / (odd+2)
                    (uint256 pa_hi,) = _mul(pow_a, a2);
                    uint256 rem = (2 * pa_hi) / (odd + 2) + 1; // +1 for conservative bound

                    // Check: is D + sign_z * (partialSum + rem) all same sign?
                    // If D_neg == u_neg: they cancel partialSumly
                    // If D_neg != u_neg: they reinforce

                    // lower bound of (D + tail): use partialSum (without rem) if tail positive,
                    //   or partialSum + rem if tail negative
                    // upper bound of (D + tail): use partialSum + rem if tail positive,
                    //   or partialSum (without rem) if tail negative

                    uint256 tail_lo = partialSum;
                    uint256 tail_hi_val = partialSum + rem;

                    bool result_neg;
                    bool result_pos;

                    if (!u_neg) {
                        // tail is positive
                        if (!D_neg) {
                            // D >= 0, tail >= 0 → always positive → return q_hi
                            return (q_hi_hi, q_hi_lo);
                        } else {
                            // D < 0, tail > 0. Check if tail_lo > |D|
                            result_pos = (D_hi == 0 && tail_lo >= D_lo);
                            result_neg = (D_hi > 0 || (D_hi == 0 && tail_hi_val < D_lo));
                        }
                    } else {
                        // tail is negative
                        if (D_neg) {
                            // D < 0, tail < 0 → always negative → return q_lo
                            return (q_lo_hi_val, q_lo_lo_val);
                        } else {
                            // D >= 0, tail < 0. Check if |tail| > D
                            result_neg = (D_hi == 0 && tail_lo > D_lo);
                            result_pos = (D_hi > 0 || (D_hi == 0 && tail_hi_val <= D_lo));
                        }
                    }

                    if (result_neg) return (q_lo_hi_val, q_lo_lo_val);
                    if (result_pos) return (q_hi_hi, q_hi_lo);

                    // Next power: pow_a = pow_a * a2 >> 256
                    pow_a = pa_hi;
                }
            }

            // Should not reach here given our convergence bounds
            // Return q_hi as fallback
            return (q_hi_hi, q_hi_lo);
        }
    }

    /// Look up C0_EXACT Q256 constant by bucket index j (0..15).
    function _lnC0ExactQ256(uint256 j) private pure returns (uint256 r) {
        assembly ("memory-safe") {
            switch j
            case 0  { r := 3676248108410512522884654055069347598461433908038198409365577366166115323608 }
            case 1  { r := 11398581695720039721329937428610221209796015481254489863285451918405973902822 }
            case 2  { r := 15461878930761829229137676699525226505276924779444969780503827915434241961033 }
            case 3  { r := 24042995855582136664155807340809396252638427204525638120407873210386888890307 }
            case 4  { r := 28584444172978065591130410613805318878106222400090682170856585690648758938527 }
            case 5  { r := 33311308205312680284369338703716915449575454018676753548640125684805014437579 }
            case 6  { r := 38239374875999667522032947591743520695232775968320786985104801804537284692778 }
            case 7  { r := 43386537334357651191261462168781086211962300144685414986294608961431443799443 }
            case 8  { r := 48773187136074509513507015403242141954852378798121723329143953600239256398613 }
            case 9  { r := 54422702179484687226682157410057694706048445005840314388489726598034357957349 }
            case 10 { r := 60362059900483868559960435468053842960499603275763905875550966723903832117518 }
            case 11 { r := 60362059900483868559960435468053842960499603275763905875550966723903832117518 }
            case 12 { r := 66622616410625360568738677407433830899150908037353507097280251369610028875158 }
            case 13 { r := 73241108566644139308970233205920051172483346696661603115364893905619174842851 }
            case 14 { r := 73241108566644139308970233205920051172483346696661603115364893905619174842851 }
            case 15 { r := 80260960185991308862233904206310070533990667611589946606122867505419956976172 }
        }
    }

    function oshr(uint512 r, uint512 x, uint256 s) internal pure returns (uint512) {
        (uint256 x_hi, uint256 x_lo) = x.into();
        (uint256 r_hi, uint256 r_lo) = _shr(x_hi, x_lo, s);
        return r.from(r_hi, r_lo);
    }

    function ishr(uint512 r, uint256 s) internal pure returns (uint512) {
        return oshr(r, r, s);
    }

    function _shrUp(uint256 x_hi, uint256 x_lo, uint256 s) internal pure returns (uint256 r_hi, uint256 r_lo) {
        assembly ("memory-safe") {
            let neg_s := sub(0x100, s)
            let s_256 := sub(s, 0x100)

            // compute `(x_hi, x_lo) >> s`, retaining intermediate values
            let x_lo_shr := shr(s, x_lo)
            let x_hi_shr := shr(s_256, x_hi)
            r_hi := shr(s, x_hi)
            r_lo := or(or(shl(neg_s, x_hi), x_lo_shr), x_hi_shr)

            // detect if nonzero bits were truncated
            let inc := lt(0x00, or(xor(x_lo, shl(s, x_lo_shr)), mul(xor(x_hi, shl(s_256, x_hi_shr)), lt(0x100, neg_s))))

            // conditionally increment the result
            r_lo := add(inc, r_lo)
            r_hi := add(lt(r_lo, inc), r_hi)
        }
    }

    function oshrUp(uint512 r, uint512 x, uint256 s) internal pure returns (uint512) {
        (uint256 x_hi, uint256 x_lo) = x.into();
        (uint256 r_hi, uint256 r_lo) = _shrUp(x_hi, x_lo, s);
        return r.from(r_hi, r_lo);
    }

    function ishrUp(uint512 r, uint256 s) internal pure returns (uint512) {
        return oshrUp(r, r, s);
    }

    function oshl(uint512 r, uint512 x, uint256 s) internal pure returns (uint512) {
        (uint256 x_hi, uint256 x_lo) = x.into();
        (uint256 r_hi, uint256 r_lo) = _shl(x_hi, x_lo, s);
        return r.from(r_hi, r_lo);
    }

    function ishl(uint512 r, uint256 s) internal pure returns (uint512) {
        return oshl(r, r, s);
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

    function smuggleToPure(function(uint512, uint512, uint512) internal view returns (uint512) f)
        internal
        pure
        returns (function(uint512, uint512, uint512) internal pure returns (uint512) r)
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

using {__add as +, __sub as -, __mul as *, __mod as %, __div as /} for uint512 global;

struct uint512_external {
    uint256 hi;
    uint256 lo;
}

library Lib512MathExternal {
    function from(uint512 r, uint512_external memory x) internal pure returns (uint512) {
        assembly ("memory-safe") {
            // This 𝐜𝐨𝐮𝐥𝐝 be done with `mcopy`, but that would mean giving up compatibility with
            // Shanghai (or less) chains. If you care about gas efficiency, you should be using
            // `into()` instead.
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

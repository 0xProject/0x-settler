// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {SlowMath} from "../SlowMath.sol";
import {Test} from "@forge-std/Test.sol";
import {FormalModelFFI} from "./FormalModelFFI.t.sol";
import {Sqrt512Wrapper} from "src/wrappers/Sqrt512Wrapper.sol";

/// @dev Fuzz-tests the generated Lean models of 512Math.sqrt and
/// 512Math.osqrtUp against the same correctness properties used in
/// 512Math.t.sol.  Calls the compiled Lean evaluator via `vm.ffi`.
///
/// Requires the `sqrt512-model` binary to be pre-built:
///   cd formal/sqrt/Sqrt512Proof && lake build sqrt512-model
contract Sqrt512ModelTest is Test, FormalModelFFI {
    string private constant _BIN = "formal/sqrt/Sqrt512Proof/.lake/build/bin/sqrt512-model";
    Sqrt512Wrapper private _wrapper;

    function setUp() external {
        _wrapper = new Sqrt512Wrapper();
    }

    // -- helpers ----------------------------------------------------------

    /// @dev 512-bit comparison: (a_hi, a_lo) > (b_hi, b_lo)
    function _gt512(uint256 aH, uint256 aL, uint256 bH, uint256 bL) internal pure returns (bool) {
        return aH > bH || (aH == bH && aL > bL);
    }

    /// @dev 512-bit comparison: (a_hi, a_lo) >= (b_hi, b_lo)
    function _ge512(uint256 aH, uint256 aL, uint256 bH, uint256 bL) internal pure returns (bool) {
        return aH > bH || (aH == bH && aL >= bL);
    }

    // -- floor sqrt: model_sqrt512_evm (x_hi > 0) ------------------------

    function testSqrt512Model(uint256 x_hi, uint256 x_lo) external {
        // _sqrt assumes x_hi != 0 (the public sqrt dispatches to 256-bit sqrt otherwise)
        vm.assume(x_hi != 0);

        uint256 r = _ffiWord512(_BIN, "sqrt512", x_hi, x_lo);

        // r^2 <= x
        (uint256 r2_lo, uint256 r2_hi) = SlowMath.fullMul(r, r);
        assertTrue(!_gt512(r2_hi, r2_lo, x_hi, x_lo), "sqrt too high");

        // (r+1)^2 > x  (unless r == max uint256)
        if (r == type(uint256).max) {
            assertTrue(
                x_hi > 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe
                    || (x_hi == 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe && x_lo != 0),
                "sqrt too low (overflow)"
            );
        } else {
            uint256 r1 = r + 1;
            (r2_lo, r2_hi) = SlowMath.fullMul(r1, r1);
            assertTrue(_gt512(r2_hi, r2_lo, x_hi, x_lo), "sqrt too low");
        }
    }

    // -- floor sqrt: model_sqrt512_wrapper_evm (full range) ---------------

    function testSqrt512WrapperModel(uint256 x_hi, uint256 x_lo) external {
        uint256 r = _ffiWord512(_BIN, "sqrt512_wrapper", x_hi, x_lo);

        // r^2 <= x
        (uint256 r2_lo, uint256 r2_hi) = SlowMath.fullMul(r, r);
        assertTrue(!_gt512(r2_hi, r2_lo, x_hi, x_lo), "wrapper sqrt too high");

        // (r+1)^2 > x
        if (r == type(uint256).max) {
            assertTrue(
                x_hi > 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe
                    || (x_hi == 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe && x_lo != 0),
                "wrapper sqrt too low (overflow)"
            );
        } else {
            uint256 r1 = r + 1;
            (r2_lo, r2_hi) = SlowMath.fullMul(r1, r1);
            assertTrue(_gt512(r2_hi, r2_lo, x_hi, x_lo), "wrapper sqrt too low");
        }
    }

    // -- ceiling sqrt: model_osqrtUp_evm ----------------------------------

    function testOsqrtUpModel(uint256 x_hi, uint256 x_lo) external {
        (uint256 r_hi, uint256 r_lo) = _ffiPair512(_BIN, "osqrtUp", x_hi, x_lo);

        // Compute r^2 = (r_hi * 2^256 + r_lo)^2
        // For the ceiling sqrt, r_hi is 0 or 1 (result fits in 257 bits max).
        // When r_hi = 0: r^2 = r_lo * r_lo (fits in 512 bits).
        // When r_hi = 1: r_lo = 0, r = 2^256, r^2 = 2^512 which overflows.
        //   This only happens when x = 2^512 - 1 (all ones), but x < 2^512.

        if (r_hi == 0) {
            // x <= r_lo^2
            (uint256 r2_lo, uint256 r2_hi) = SlowMath.fullMul(r_lo, r_lo);
            assertTrue(_ge512(r2_hi, r2_lo, x_hi, x_lo), "osqrtUp too low");

            // (r_lo - 1)^2 < x  (r_lo is minimal)
            if (r_lo > 0) {
                (uint256 rm2_lo, uint256 rm2_hi) = SlowMath.fullMul(r_lo - 1, r_lo - 1);
                assertTrue(!_ge512(rm2_hi, rm2_lo, x_hi, x_lo), "osqrtUp too high");
            } else {
                // r = 0, x must be 0
                assertEq(x_hi, 0, "osqrtUp r=0 but x_hi!=0");
                assertEq(x_lo, 0, "osqrtUp r=0 but x_lo!=0");
            }
        } else {
            // r_hi = 1, r = 2^256. x <= (2^256)^2 = 2^512 which always holds.
            // But x must be > (2^256 - 1)^2 = 2^512 - 2^257 + 1.
            assertEq(r_hi, 1, "osqrtUp r_hi > 1");
            assertEq(r_lo, 0, "osqrtUp r_hi=1 but r_lo!=0");
            // (2^256 - 1)^2 < x
            uint256 rM = type(uint256).max;
            (uint256 rm2_lo, uint256 rm2_hi) = SlowMath.fullMul(rM, rM);
            assertTrue(_gt512(x_hi, x_lo, rm2_hi, rm2_lo), "osqrtUp too high (r=2^256)");
        }
    }

    function testDiffSqrt512Wrapper(uint256 x_hi, uint256 x_lo) external {
        assertEq(_wrapper.wrap_sqrt512(x_hi, x_lo), _ffiWord512(_BIN, "sqrt512_wrapper", x_hi, x_lo));
    }

    function testDiffOsqrtUp(uint256 x_hi, uint256 x_lo) external {
        (uint256 model_hi, uint256 model_lo) = _ffiPair512(_BIN, "osqrtUp", x_hi, x_lo);
        (uint256 wrapper_hi, uint256 wrapper_lo) = _wrapper.wrap_osqrtUp(x_hi, x_lo);
        assertEq(wrapper_hi, model_hi);
        assertEq(wrapper_lo, model_lo);
    }
}

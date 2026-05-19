// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {uint512, alloc} from "src/utils/512Math.sol";
import {Test} from "@forge-std/Test.sol";
import {FormalModelFFI} from "./FormalModelFFI.t.sol";
import {Cbrt512Wrapper} from "src/wrappers/Cbrt512Wrapper.sol";

/// @dev Fuzz-tests the generated Lean models of 512Math._cbrt, cbrt, and cbrtUp
/// against correctness properties. Uses uint512 arithmetic for cubing and
/// special-cases the overflow regime where (r_max+1)³ exceeds 512 bits,
/// matching 512Math.t.sol.
///
/// Requires the `cbrt512-model` binary to be pre-built:
///   cd formal/cbrt/Cbrt512Proof && lake build cbrt512-model
contract Cbrt512ModelTest is Test, FormalModelFFI {
    string private constant _BIN = "formal/cbrt/Cbrt512Proof/.lake/build/bin/cbrt512-model";
    Cbrt512Wrapper private _wrapper;

    // r_max is the largest value whose cube fits in 512 bits. _cbrt is pinned
    // at r_max for x >= r_max³; see the overflow-regime note in 512Math.sol.
    uint256 private constant R_MAX = 0x6597fa94f5b8f20ac16666ad0f7137bc6601d885628;
    uint256 private constant R_MAX_CUBE_HI = 0xffffffffffffffffffffffffffffffffffffffffffec2567f7d10a5e1c63772f;
    uint256 private constant R_MAX_CUBE_LO = 0xd70b34358c5c72dd2dbdc27132d143e3a7f08c1088df427db0884640df2d7a00;

    function setUp() external {
        _wrapper = new Cbrt512Wrapper();
    }

    // -- _cbrt model: within 1ulp (not exact floor) --------------------------
    // _cbrt returns icbrt(x) or icbrt(x)+1. We check (r-1)³ ≤ x < (r+1)³.
    // When r ≥ R_MAX, (r+1)³ overflows, so we skip the upper bound check.

    function testCbrt512Model(uint256 x_hi, uint256 x_lo) external {
        vm.assume(x_hi != 0);

        uint256 r = _ffiWord512(_BIN, "cbrt512", x_hi, x_lo);
        uint512 x = alloc().from(x_hi, x_lo);

        // Lower bound: (r-1)³ ≤ x
        if (r > 0) {
            uint256 rm = r - 1;
            uint512 r3m = alloc().omul(rm, rm).imul(rm);
            assertTrue(r3m <= x, "cbrt model: (r-1)^3 > x");
        }

        // Upper bound: (r+1)³ > x — only when r < R_MAX (avoids 513-bit overflow)
        if (r < R_MAX) {
            uint256 r1 = r + 1;
            uint512 r3p = alloc().omul(r1, r1).imul(r1);
            assertTrue(r3p > x, "cbrt model: (r+1)^3 <= x");
        }
    }

    // -- cbrt wrapper: exact floor --------------------------------------------
    // Matches 512Math.t.sol::test512Math_cbrt: for x >= r_max³, assert r == r_max.

    function testCbrt512WrapperModel(uint256 x_hi, uint256 x_lo) external {
        uint256 r = _ffiWord512(_BIN, "cbrt512_wrapper", x_hi, x_lo);
        uint512 x = alloc().from(x_hi, x_lo);

        // r³ ≤ x
        uint512 r3 = alloc().omul(r, r).imul(r);
        assertTrue(r3 <= x, "wrapper cbrt too high: r^3 > x");

        // (r+1)³ > x — in the overflow regime (x >= r_max³), check r == r_max instead
        if (
            x_hi > R_MAX_CUBE_HI
                || (x_hi == R_MAX_CUBE_HI && x_lo > R_MAX_CUBE_LO - 1)
        ) {
            assertEq(r, R_MAX, "wrapper cbrt overflow");
        } else {
            r++;
            r3.omul(r, r).imul(r);
            assertTrue(r3 > x, "wrapper cbrt too low: (r+1)^3 <= x");
        }
    }

    // -- cbrtUp wrapper: exact ceiling ----------------------------------------
    // Matches 512Math.t.sol::test512Math_cbrtUp: for x > r_max³, assert r == r_max+1.

    function testCbrtUp512Model(uint256 x_hi, uint256 x_lo) external {
        uint256 r = _ffiWord512(_BIN, "cbrtUp512_wrapper", x_hi, x_lo);
        uint512 x = alloc().from(x_hi, x_lo);
        uint512 r3 = alloc().omul(r, r).imul(r);

        // r³ ≥ x — in the overflow regime (x > r_max³), check r == r_max+1 instead
        if (
            x_hi > R_MAX_CUBE_HI
                || (x_hi == R_MAX_CUBE_HI && x_lo > R_MAX_CUBE_LO)
        ) {
            assertEq(r, R_MAX + 1, "cbrtUp overflow");
        } else {
            assertTrue(r3 >= x, "cbrtUp too low: r^3 < x");
        }

        // (r-1)³ < x (minimality)
        if (x_hi != 0 || x_lo != 0) {
            uint256 rm = r - 1;
            r3.omul(rm, rm).imul(rm);
            assertTrue(r3 < x, "cbrtUp too high: (r-1)^3 >= x");
        }
    }

    function testDiffCbrt512Wrapper(uint256 x_hi, uint256 x_lo) external {
        assertEq(_wrapper.wrap_cbrt512(x_hi, x_lo), _ffiWord512(_BIN, "cbrt512_wrapper", x_hi, x_lo));
    }

    function testDiffCbrtUp512Wrapper(uint256 x_hi, uint256 x_lo) external {
        assertEq(
            _wrapper.wrap_cbrtUp512(x_hi, x_lo),
            _ffiWord512(_BIN, "cbrtUp512_wrapper", x_hi, x_lo)
        );
    }
}

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {uint512, alloc, tmp} from "src/utils/512Math.sol";
import {SlowMath} from "./SlowMath.sol";

import {Test} from "@forge-std/Test.sol";

contract Lib512MathTest is Test {
    function test512Math_oaddBothForeign(uint256 x, uint256 y) external pure {
        (uint256 r_hi, uint256 r_lo) = tmp().oadd(x, y).into();
        (uint256 e_lo, uint256 e_hi) = SlowMath.fullAdd(x, 0, y, 0);
        assertEq(r_hi, e_hi);
        assertEq(r_lo, e_lo);
    }

    function test512Math_oaddForeign(uint256 x_hi, uint256 x_lo, uint256 y) external pure {
        uint512 x = alloc().from(x_hi, x_lo);
        (uint256 r_hi, uint256 r_lo) = tmp().oadd(x, y).into();
        (uint256 e_lo, uint256 e_hi) = SlowMath.fullAdd(x_lo, x_hi, y, 0);
        assertEq(r_hi, e_hi);
        assertEq(r_lo, e_lo);
    }

    function test512Math_iaddForeign(uint256 x_hi, uint256 x_lo, uint256 y) external pure {
        (uint256 r_hi, uint256 r_lo) = tmp().from(x_hi, x_lo).iadd(y).into();
        (uint256 e_lo, uint256 e_hi) = SlowMath.fullAdd(x_lo, x_hi, y, 0);
        assertEq(r_hi, e_hi);
        assertEq(r_lo, e_lo);
    }

    function test512Math_oaddNative(uint256 x_hi, uint256 x_lo, uint256 y_hi, uint256 y_lo) external pure {
        uint512 x = alloc().from(x_hi, x_lo);
        uint512 y = alloc().from(y_hi, y_lo);
        (uint256 r_hi, uint256 r_lo) = tmp().oadd(x, y).into();
        (uint256 e_lo, uint256 e_hi) = SlowMath.fullAdd(x_lo, x_hi, y_lo, y_hi);
        assertEq(r_hi, e_hi);
        assertEq(r_lo, e_lo);
    }

    function test512Math_iaddNative(uint256 x_hi, uint256 x_lo, uint256 y_hi, uint256 y_lo) external pure {
        uint512 y = alloc().from(y_hi, y_lo);
        (uint256 r_hi, uint256 r_lo) = tmp().from(x_hi, x_lo).iadd(y).into();
        (uint256 e_lo, uint256 e_hi) = SlowMath.fullAdd(x_lo, x_hi, y_lo, y_hi);
        assertEq(r_hi, e_hi);
        assertEq(r_lo, e_lo);
    }

    function test512Math_osubForeign(uint256 x_hi, uint256 x_lo, uint256 y) external pure {
        vm.assume(x_hi > 0 || x_lo >= y);
        uint512 x = alloc().from(x_hi, x_lo);
        (uint256 r_hi, uint256 r_lo) = tmp().osub(x, y).into();
        (uint256 e_lo, uint256 e_hi) = SlowMath.fullSub(x_lo, x_hi, y, 0);
        assertEq(r_hi, e_hi);
        assertEq(r_lo, e_lo);
    }

    function test512Math_isubForeign(uint256 x_hi, uint256 x_lo, uint256 y) external pure {
        vm.assume(x_hi > 0 || x_lo >= y);
        (uint256 r_hi, uint256 r_lo) = tmp().from(x_hi, x_lo).isub(y).into();
        (uint256 e_lo, uint256 e_hi) = SlowMath.fullSub(x_lo, x_hi, y, 0);
        assertEq(r_hi, e_hi);
        assertEq(r_lo, e_lo);
    }

    function test512Math_osubNative(uint256 x_hi, uint256 x_lo, uint256 y_hi, uint256 y_lo) external pure {
        vm.assume(x_hi > y_hi || (x_hi == y_hi && x_lo >= y_lo));
        uint512 x = alloc().from(x_hi, x_lo);
        uint512 y = alloc().from(y_hi, y_lo);
        (uint256 r_hi, uint256 r_lo) = tmp().osub(x, y).into();
        (uint256 e_lo, uint256 e_hi) = SlowMath.fullSub(x_lo, x_hi, y_lo, y_hi);
        assertEq(r_hi, e_hi);
        assertEq(r_lo, e_lo);
    }

    function test512Math_isubNative(uint256 x_hi, uint256 x_lo, uint256 y_hi, uint256 y_lo) external pure {
        vm.assume(x_hi > y_hi || (x_hi == y_hi && x_lo >= y_lo));
        uint512 y = alloc().from(y_hi, y_lo);
        (uint256 r_hi, uint256 r_lo) = tmp().from(x_hi, x_lo).isub(y).into();
        (uint256 e_lo, uint256 e_hi) = SlowMath.fullSub(x_lo, x_hi, y_lo, y_hi);
        assertEq(r_hi, e_hi);
        assertEq(r_lo, e_lo);
    }

    function test512Math_omulBothForeign(uint256 x, uint256 y) external pure {
        (uint256 r_hi, uint256 r_lo) = tmp().omul(x, y).into();
        (uint256 e_lo, uint256 e_hi) = SlowMath.fullMul(x, y);
        assertEq(r_hi, e_hi);
        assertEq(r_lo, e_lo);
    }

    function test512Math_omulForeign(uint256 x_hi, uint256 x_lo, uint256 y) external pure {
        uint512 x = alloc().from(x_hi, x_lo);
        (uint256 r_hi, uint256 r_lo) = tmp().omul(x, y).into();
        (uint256 e_lo, uint256 e_hi) = SlowMath.fullMul(x_lo, x_hi, y, 0);
        assertEq(r_hi, e_hi);
        assertEq(r_lo, e_lo);
    }

    function test512Math_imulForeign(uint256 x_hi, uint256 x_lo, uint256 y) external pure {
        (uint256 r_hi, uint256 r_lo) = tmp().from(x_hi, x_lo).imul(y).into();
        (uint256 e_lo, uint256 e_hi) = SlowMath.fullMul(x_lo, x_hi, y, 0);
        assertEq(r_hi, e_hi);
        assertEq(r_lo, e_lo);
    }

    function test512Math_omulNative(uint256 x_hi, uint256 x_lo, uint256 y_hi, uint256 y_lo) external pure {
        uint512 x = alloc().from(x_hi, x_lo);
        uint512 y = alloc().from(y_hi, y_lo);
        (uint256 r_hi, uint256 r_lo) = tmp().omul(x, y).into();
        (uint256 e_lo, uint256 e_hi) = SlowMath.fullMul(x_lo, x_hi, y_lo, y_hi);
        assertEq(r_hi, e_hi);
        assertEq(r_lo, e_lo);
    }

    function test512Math_imulNative(uint256 x_hi, uint256 x_lo, uint256 y_hi, uint256 y_lo) external pure {
        uint512 y = alloc().from(y_hi, y_lo);
        (uint256 r_hi, uint256 r_lo) = tmp().from(x_hi, x_lo).imul(y).into();
        (uint256 e_lo, uint256 e_hi) = SlowMath.fullMul(x_lo, x_hi, y_lo, y_hi);
        assertEq(r_hi, e_hi);
        assertEq(r_lo, e_lo);
    }

    function test512Math_mod(uint256 x_hi, uint256 x_lo, uint256 y) external pure {
        vm.assume(y != 0);
        uint256 r = tmp().from(x_hi, x_lo).mod(y);
        (uint256 e_lo, uint256 e_hi) = SlowMath.fullDiv(x_lo, x_hi, y);
        (e_lo, e_hi) = SlowMath.fullMul(e_lo, e_hi, y, 0);
        (e_lo, e_hi) = SlowMath.fullSub(x_lo, x_hi, e_lo, e_hi);
        assertEq(r, e_lo);
        assertEq(e_hi, 0);
    }

    // omod and imod don't have test cases because I don't have a way to derive
    // a reference implementation without using 512Math's division routines

    function test512Math_divForeign(uint256 x_hi, uint256 x_lo, uint256 y) external pure {
        vm.assume(y != 0);
        uint256 r_lo = tmp().from(x_hi, x_lo).div(y);
        (uint256 e_lo,) = SlowMath.fullDiv(x_lo, x_hi, y);
        assertEq(r_lo, e_lo);
    }

    function test512Math_divNative(uint256 x_hi, uint256 x_lo, uint256 y_hi, uint256 y_lo) external view {
        vm.assume(y_hi != 0);
        uint512 x = alloc().from(x_hi, x_lo);
        uint512 y = alloc().from(y_hi, y_lo);
        uint256 q = x.div(y);
        (uint256 e_lo, uint256 e_hi) = SlowMath.fullMul(y_lo, y_hi, q, 0);
        uint512 e = alloc().from(e_hi, e_lo);
        assertTrue(e <= x);
        assertTrue((q == 0 && x < y) || e > tmp().osub(x, y));
    }

    function test512Math_odivForeign(uint256 x_hi, uint256 x_lo, uint256 y) external pure {
        vm.assume(y != 0);
        uint512 x = alloc().from(x_hi, x_lo);
        (uint256 r_hi, uint256 r_lo) = tmp().odiv(x, y).into();
        (uint256 e_lo, uint256 e_hi) = SlowMath.fullDiv(x_lo, x_hi, y);
        assertEq(r_hi, e_hi);
        assertEq(r_lo, e_lo);
    }

    function test512Math_idivForeign(uint256 x_hi, uint256 x_lo, uint256 y) external pure {
        vm.assume(y != 0);
        (uint256 r_hi, uint256 r_lo) = tmp().from(x_hi, x_lo).idiv(y).into();
        (uint256 e_lo, uint256 e_hi) = SlowMath.fullDiv(x_lo, x_hi, y);
        assertEq(r_hi, e_hi);
        assertEq(r_lo, e_lo);
    }

    function test512Math_odivNative(uint256 x_hi, uint256 x_lo, uint256 y_hi, uint256 y_lo) external view {
        vm.assume(y_hi != 0);

        uint512 x = alloc().from(x_hi, x_lo);
        uint512 y = alloc().from(y_hi, y_lo);
        (uint256 r_hi, uint256 r_lo) = tmp().odiv(x, y).into();

        (uint256 e_lo, uint256 e_hi) = SlowMath.fullMul(y_lo, y_hi, r_lo, r_hi);
        uint512 e = alloc().from(e_hi, e_lo);
        assertTrue(e <= x);
        assertTrue((r_hi == 0 && r_lo == 0 && x < y) || e > tmp().osub(x, y));
    }

    function test512Math_idivNative(uint256 x_hi, uint256 x_lo, uint256 y_hi, uint256 y_lo) external view {
        vm.assume(y_hi != 0);

        uint512 x = alloc().from(x_hi, x_lo);
        uint512 y = alloc().from(y_hi, y_lo);
        (uint256 r_hi, uint256 r_lo) = tmp().from(x).idiv(y).into();

        (uint256 e_lo, uint256 e_hi) = SlowMath.fullMul(y_lo, y_hi, r_lo, r_hi);
        uint512 e = alloc().from(e_hi, e_lo);
        assertTrue(e <= x);
        assertTrue((r_hi == 0 && r_lo == 0 && x < y) || e > tmp().osub(x, y));
    }

    function test512Math_odivAlt(uint256 x_hi, uint256 x_lo, uint256 y_hi, uint256 y_lo) external pure {
        vm.assume(y_hi != 0);

        uint512 x = alloc().from(x_hi, x_lo);
        uint512 y = alloc().from(y_hi, y_lo);
        (uint256 r_hi, uint256 r_lo) = tmp().odivAlt(x, y).into();

        (uint256 e_lo, uint256 e_hi) = SlowMath.fullMul(y_lo, y_hi, r_lo, r_hi);
        uint512 e = alloc().from(e_hi, e_lo);
        assertTrue(e <= x);
        assertTrue((r_hi == 0 && r_lo == 0 && x < y) || e > tmp().osub(x, y));
    }

    function test512Math_omodAlt(uint256 x_hi, uint256 x_lo, uint256 y_hi, uint256 y_lo) external view {
        vm.assume(y_hi != 0);

        uint512 x = alloc().from(x_hi, x_lo);
        uint512 y = alloc().from(y_hi, y_lo);
        uint512 r = alloc().omodAlt(x, y);
        uint512 e = alloc().omod(x, y);

        assertTrue(r == e);
    }

    function test512Math_sqrt(uint256 x_hi, uint256 x_lo) external pure {
        uint512 x = alloc().from(x_hi, x_lo);
        uint256 r = x.sqrt();

        (uint256 r2_lo, uint256 r2_hi) = SlowMath.fullMul(r, r);
        assertTrue((r2_hi < x_hi) || (r2_hi == x_hi && r2_lo <= x_lo), "sqrt too high");

        if (r == type(uint256).max) {
            assertTrue(
                x_hi > 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe
                    || (x_hi == 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe && x_lo != 0),
                "sqrt too low (overflow)"
            );
        } else {
            r++;
            (r2_lo, r2_hi) = SlowMath.fullMul(r, r);
            assertTrue((r2_hi > x_hi) || (r2_hi == x_hi && r2_lo > x_lo), "sqrt too low");
        }
    }

    function test512Math_divUpAlt(uint256 x_hi, uint256 x_lo, uint256 y_hi, uint256 y_lo) external view {
        vm.assume(y_hi != 0);

        uint512 x = alloc().from(x_hi, x_lo);
        uint512 y = alloc().from(y_hi, y_lo);

        uint256 ceil_q = x.divUpAlt(y);
        uint256 floor_q = x.div(y);

        (uint256 e_lo, uint256 e_hi) = SlowMath.fullMul(y_lo, y_hi, floor_q, 0);
        uint512 e = alloc().from(e_hi, e_lo);

        assertTrue(
            ceil_q == floor_q || (floor_q == type(uint256).max && ceil_q == 0) || (e != x && ceil_q == floor_q + 1)
        );
    }

    function test512Math_odivUpAlt(uint256 x_hi, uint256 x_lo, uint256 y_hi, uint256 y_lo) external view {
        vm.assume(y_hi != 0);

        uint512 x = alloc().from(x_hi, x_lo);
        uint512 y = alloc().from(y_hi, y_lo);

        uint512 ceil_q = alloc().odivUpAlt(x, y);
        uint512 floor_q = alloc().odiv(x, y);

        (uint256 floor_q_hi, uint256 floor_q_lo) = floor_q.into();
        (uint256 e_lo, uint256 e_hi) = SlowMath.fullMul(y_lo, y_hi, floor_q_lo, floor_q_hi);
        uint512 e = alloc().from(e_hi, e_lo);

        assertTrue(
            ceil_q == floor_q
                || (floor_q == tmp().from(type(uint256).max, type(uint256).max) && ceil_q == tmp().from(0, 0))
                || (e != x && ceil_q == tmp().oadd(floor_q, 1))
        );
    }

    function test512Math_divUpForeign(uint256 x_hi, uint256 x_lo, uint256 y) external pure {
        vm.assume(y != 0);

        uint512 x = alloc().from(x_hi, x_lo);

        uint256 ceil_q = x.divUp(y);
        uint256 floor_q = x.div(y);

        (uint256 e_lo, uint256 e_hi) = SlowMath.fullMul(y, floor_q);
        uint512 e = alloc().from(e_hi, e_lo);

        assertTrue(
            ceil_q == floor_q || (floor_q == type(uint256).max && ceil_q == 0) || (e != x && ceil_q == floor_q + 1)
        );
    }

    function test512Math_divUpNative(uint256 x_hi, uint256 x_lo, uint256 y_hi, uint256 y_lo) external view {
        vm.assume(y_hi != 0);

        uint512 x = alloc().from(x_hi, x_lo);
        uint512 y = alloc().from(y_hi, y_lo);

        uint256 ceil_q = x.divUp(y);
        uint256 floor_q = x.div(y);

        (uint256 e_lo, uint256 e_hi) = SlowMath.fullMul(y_lo, y_hi, floor_q, 0);
        uint512 e = alloc().from(e_hi, e_lo);

        assertTrue(
            ceil_q == floor_q || (floor_q == type(uint256).max && ceil_q == 0) || (e != x && ceil_q == floor_q + 1)
        );
    }

    function test512Math_odivUpForeign(uint256 x_hi, uint256 x_lo, uint256 y) external pure {
        vm.assume(y != 0);

        uint512 x = alloc().from(x_hi, x_lo);

        uint512 ceil_q = alloc().odivUp(x, y);
        uint512 floor_q = alloc().odiv(x, y);

        (uint256 floor_q_hi, uint256 floor_q_lo) = floor_q.into();
        (uint256 e_lo, uint256 e_hi) = SlowMath.fullMul(y, 0, floor_q_lo, floor_q_hi);
        uint512 e = alloc().from(e_hi, e_lo);

        assertTrue(
            ceil_q == floor_q
                || (floor_q == tmp().from(type(uint256).max, type(uint256).max) && ceil_q == tmp().from(0, 0))
                || (e != x && ceil_q == tmp().oadd(floor_q, 1))
        );
    }

    function test512Math_idivUpForeign(uint256 x_hi, uint256 x_lo, uint256 y) external pure {
        vm.assume(y != 0);

        uint512 x = alloc().from(x_hi, x_lo);

        (uint256 ceil_q_hi, uint256 ceil_q_lo) = tmp().from(x).idivUp(y).into();
        (uint256 floor_q_hi, uint256 floor_q_lo) = tmp().from(x).idiv(y).into();

        (uint256 e_lo, uint256 e_hi) = SlowMath.fullMul(y, 0, floor_q_lo, floor_q_hi);
        uint512 e = alloc().from(e_hi, e_lo);

        uint512 ceil_q = alloc().from(ceil_q_hi, ceil_q_lo);
        uint512 floor_q = alloc().from(floor_q_hi, floor_q_lo);

        assertTrue(
            ceil_q == floor_q
                || (floor_q == tmp().from(type(uint256).max, type(uint256).max) && ceil_q == tmp().from(0, 0))
                || (e != x && ceil_q == tmp().oadd(floor_q, 1))
        );
    }

    function test512Math_odivUpNative(uint256 x_hi, uint256 x_lo, uint256 y_hi, uint256 y_lo) external view {
        vm.assume(y_hi != 0);

        uint512 x = alloc().from(x_hi, x_lo);
        uint512 y = alloc().from(y_hi, y_lo);

        uint512 ceil_q = alloc().odivUp(x, y);
        uint512 floor_q = alloc().odiv(x, y);

        (uint256 floor_q_hi, uint256 floor_q_lo) = floor_q.into();
        (uint256 e_lo, uint256 e_hi) = SlowMath.fullMul(y_lo, y_hi, floor_q_lo, floor_q_hi);
        uint512 e = alloc().from(e_hi, e_lo);

        assertTrue(
            ceil_q == floor_q
                || (floor_q == tmp().from(type(uint256).max, type(uint256).max) && ceil_q == tmp().from(0, 0))
                || (e != x && ceil_q == tmp().oadd(floor_q, 1))
        );
    }

    function test512Math_idivUpNative(uint256 x_hi, uint256 x_lo, uint256 y_hi, uint256 y_lo) external view {
        vm.assume(y_hi != 0);

        uint512 x = alloc().from(x_hi, x_lo);
        uint512 y = alloc().from(y_hi, y_lo);

        (uint256 ceil_q_hi, uint256 ceil_q_lo) = tmp().from(x).idivUp(y).into();
        (uint256 floor_q_hi, uint256 floor_q_lo) = tmp().from(x).idiv(y).into();

        (uint256 e_lo, uint256 e_hi) = SlowMath.fullMul(y_lo, y_hi, floor_q_lo, floor_q_hi);
        uint512 e = alloc().from(e_hi, e_lo);

        uint512 ceil_q = alloc().from(ceil_q_hi, ceil_q_lo);
        uint512 floor_q = alloc().from(floor_q_hi, floor_q_lo);

        assertTrue(
            ceil_q == floor_q
                || (floor_q == tmp().from(type(uint256).max, type(uint256).max) && ceil_q == tmp().from(0, 0))
                || (e != x && ceil_q == tmp().oadd(floor_q, 1))
        );
    }

    function test512Math_osqrtUp(uint256 x_hi, uint256 x_lo) external pure {
        uint512 x = alloc().from(x_hi, x_lo);
        (uint256 r_hi, uint256 r_lo) = alloc().osqrtUp(x).into();

        if (r_hi == 0 && r_lo == 0) {
            // sqrtUp(0) = 0
            assertTrue(x_hi == 0 && x_lo == 0, "sqrtUp of nonzero is zero");
        } else if (r_hi != 0) {
            // r >= 2^256, which means r must be exactly 2^256 (since sqrt of 512-bit is at most 2^256)
            // r^2 = 2^512 exceeds max 512-bit value, so r^2 >= x is trivially true
            // We only need to verify (r-1)^2 < x, i.e., (type(uint256).max)^2 < x
            assertTrue(r_hi == 1 && r_lo == 0, "overflow result must be exactly 2^256");
            (uint256 r_dec2_lo, uint256 r_dec2_hi) = SlowMath.fullMul(type(uint256).max, type(uint256).max);
            assertTrue((r_dec2_hi < x_hi) || (r_dec2_hi == x_hi && r_dec2_lo < x_lo), "sqrtUp too high");
        } else {
            // Normal case: r fits in 256 bits
            (uint256 r2_lo, uint256 r2_hi) = SlowMath.fullMul(r_lo, r_lo);
            assertTrue((r2_hi > x_hi) || (r2_hi == x_hi && r2_lo >= x_lo), "sqrtUp too low");

            // Check (r-1)^2 < x
            if (r_lo == 1) {
                // (r-1)^2 = 0, which must be less than any nonzero x. Already verified x != 0
                // since we're in the r != 0 branch.
            } else {
                uint256 r_dec_lo = r_lo - 1;
                (r2_lo, r2_hi) = SlowMath.fullMul(r_dec_lo, r_dec_lo);
                assertTrue((r2_hi < x_hi) || (r2_hi == x_hi && r2_lo < x_lo), "sqrtUp too high");
            }
        }
    }

    function test512Math_oshrUp(uint256 x_hi, uint256 x_lo, uint256 s) external pure {
        s = bound(s, 0, 512);

        uint512 x = alloc().from(x_hi, x_lo);
        (uint256 r_hi, uint256 r_lo) = tmp().oshrUp(x, s).into();

        (uint256 e_lo, uint256 e_hi) = SlowMath.fullShrUp(x_lo, x_hi, s);
        assertEq(r_hi, e_hi);
        assertEq(r_lo, e_lo);
    }

    function test512Math_ishrUp(uint256 x_hi, uint256 x_lo, uint256 s) external pure {
        s = bound(s, 0, 512);

        (uint256 r_hi, uint256 r_lo) = tmp().from(x_hi, x_lo).ishrUp(s).into();

        (uint256 e_lo, uint256 e_hi) = SlowMath.fullShrUp(x_lo, x_hi, s);
        assertEq(r_hi, e_hi);
        assertEq(r_lo, e_lo);
    }
}

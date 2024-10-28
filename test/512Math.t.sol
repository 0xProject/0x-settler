// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {uint512, tmp_uint512} from "src/utils/512Math.sol";
import {SlowMath} from "./SlowMath.sol";

import {Test} from "@forge-std/Test.sol";

contract Lib512MathTest is Test {
    function test512Math_oaddBothForeign(uint256 x, uint256 y) external pure {
        (uint256 r_hi, uint256 r_lo) = tmp_uint512().oadd(x, y).into();
        (uint256 e_lo, uint256 e_hi) = SlowMath.fullAdd(x, 0, y, 0);
        assertEq(r_hi, e_hi);
        assertEq(r_lo, e_lo);
    }

    function test512Math_oaddForeign(uint256 x_hi, uint256 x_lo, uint256 y) external pure {
        uint512 memory x;
        x.from(x_hi, x_lo);
        (uint256 r_hi, uint256 r_lo) = tmp_uint512().oadd(x, y).into();
        (uint256 e_lo, uint256 e_hi) = SlowMath.fullAdd(x_lo, x_hi, y, 0);
        assertEq(r_hi, e_hi);
        assertEq(r_lo, e_lo);
    }

    function test512Math_iaddForeign(uint256 x_hi, uint256 x_lo, uint256 y) external pure {
        (uint256 r_hi, uint256 r_lo) = tmp_uint512().from(x_hi, x_lo).iadd(y).into();
        (uint256 e_lo, uint256 e_hi) = SlowMath.fullAdd(x_lo, x_hi, y, 0);
        assertEq(r_hi, e_hi);
        assertEq(r_lo, e_lo);
    }

    function test512Math_oaddNative(uint256 x_hi, uint256 x_lo, uint256 y_hi, uint256 y_lo) external pure {
        uint512 memory x;
        x.from(x_hi, x_lo);
        uint512 memory y;
        y.from(y_hi, y_lo);
        (uint256 r_hi, uint256 r_lo) = tmp_uint512().oadd(x, y).into();
        (uint256 e_lo, uint256 e_hi) = SlowMath.fullAdd(x_lo, x_hi, y_lo, y_hi);
        assertEq(r_hi, e_hi);
        assertEq(r_lo, e_lo);
    }

    function test512Math_iaddNative(uint256 x_hi, uint256 x_lo, uint256 y_hi, uint256 y_lo) external pure {
        uint512 memory y;
        y.from(y_hi, y_lo);
        (uint256 r_hi, uint256 r_lo) = tmp_uint512().from(x_hi, x_lo).iadd(y).into();
        (uint256 e_lo, uint256 e_hi) = SlowMath.fullAdd(x_lo, x_hi, y_lo, y_hi);
        assertEq(r_hi, e_hi);
        assertEq(r_lo, e_lo);
    }

    function test512Math_osubForeign(uint256 x_hi, uint256 x_lo, uint256 y) external pure {
        vm.assume(x_hi > 0 || x_lo >= y);
        uint512 memory x;
        x.from(x_hi, x_lo);
        (uint256 r_hi, uint256 r_lo) = tmp_uint512().osub(x, y).into();
        (uint256 e_lo, uint256 e_hi) = SlowMath.fullSub(x_lo, x_hi, y, 0);
        assertEq(r_hi, e_hi);
        assertEq(r_lo, e_lo);
    }

    function test512Math_isubForeign(uint256 x_hi, uint256 x_lo, uint256 y) external pure {
        vm.assume(x_hi > 0 || x_lo >= y);
        (uint256 r_hi, uint256 r_lo) = tmp_uint512().from(x_hi, x_lo).isub(y).into();
        (uint256 e_lo, uint256 e_hi) = SlowMath.fullSub(x_lo, x_hi, y, 0);
        assertEq(r_hi, e_hi);
        assertEq(r_lo, e_lo);
    }

    function test512Math_osubNative(uint256 x_hi, uint256 x_lo, uint256 y_hi, uint256 y_lo) external pure {
        vm.assume(x_hi > y_hi || (x_hi == y_hi && x_lo >= y_lo));
        uint512 memory x;
        x.from(x_hi, x_lo);
        uint512 memory y;
        y.from(y_hi, y_lo);
        (uint256 r_hi, uint256 r_lo) = tmp_uint512().osub(x, y).into();
        (uint256 e_lo, uint256 e_hi) = SlowMath.fullSub(x_lo, x_hi, y_lo, y_hi);
        assertEq(r_hi, e_hi);
        assertEq(r_lo, e_lo);
    }

    function test512Math_isubNative(uint256 x_hi, uint256 x_lo, uint256 y_hi, uint256 y_lo) external pure {
        vm.assume(x_hi > y_hi || (x_hi == y_hi && x_lo >= y_lo));
        uint512 memory y;
        y.from(y_hi, y_lo);
        (uint256 r_hi, uint256 r_lo) = tmp_uint512().from(x_hi, x_lo).isub(y).into();
        (uint256 e_lo, uint256 e_hi) = SlowMath.fullSub(x_lo, x_hi, y_lo, y_hi);
        assertEq(r_hi, e_hi);
        assertEq(r_lo, e_lo);
    }

    function test512Math_omulBothForeign(uint256 x, uint256 y) external pure {
        (uint256 r_hi, uint256 r_lo) = tmp_uint512().omul(x, y).into();
        (uint256 e_lo, uint256 e_hi) = SlowMath.fullMul(x, y);
        assertEq(r_hi, e_hi);
        assertEq(r_lo, e_lo);
    }

    function test512Math_omulForeign(uint256 x_hi, uint256 x_lo, uint256 y) external pure {
        uint512 memory x;
        x.from(x_hi, x_lo);
        (uint256 r_hi, uint256 r_lo) = tmp_uint512().omul(x, y).into();
        (uint256 e_lo, uint256 e_hi) = SlowMath.fullMul(x_lo, x_hi, y, 0);
        assertEq(r_hi, e_hi);
        assertEq(r_lo, e_lo);
    }

    function test512Math_imulForeign(uint256 x_hi, uint256 x_lo, uint256 y) external pure {
        (uint256 r_hi, uint256 r_lo) = tmp_uint512().from(x_hi, x_lo).imul(y).into();
        (uint256 e_lo, uint256 e_hi) = SlowMath.fullMul(x_lo, x_hi, y, 0);
        assertEq(r_hi, e_hi);
        assertEq(r_lo, e_lo);
    }

    function test512Math_omulNative(uint256 x_hi, uint256 x_lo, uint256 y_hi, uint256 y_lo) external pure {
        uint512 memory x;
        x.from(x_hi, x_lo);
        uint512 memory y;
        y.from(y_hi, y_lo);
        (uint256 r_hi, uint256 r_lo) = tmp_uint512().omul(x, y).into();
        (uint256 e_lo, uint256 e_hi) = SlowMath.fullMul(x_lo, x_hi, y_lo, y_hi);
        assertEq(r_hi, e_hi);
        assertEq(r_lo, e_lo);
    }

    function test512Math_imulNative(uint256 x_hi, uint256 x_lo, uint256 y_hi, uint256 y_lo) external pure {
        uint512 memory y;
        y.from(y_hi, y_lo);
        (uint256 r_hi, uint256 r_lo) = tmp_uint512().from(x_hi, x_lo).imul(y).into();
        (uint256 e_lo, uint256 e_hi) = SlowMath.fullMul(x_lo, x_hi, y_lo, y_hi);
        assertEq(r_hi, e_hi);
        assertEq(r_lo, e_lo);
    }

    function test512Math_div(uint256 x_hi, uint256 x_lo, uint256 y) external pure {
        vm.assume(y != 0);
        uint256 r_lo = tmp_uint512().from(x_hi, x_lo).div(y);
        (uint256 e_lo,) = SlowMath.fullDiv(x_lo, x_hi, y);
        assertEq(r_lo, e_lo);
    }

    function test512Math_odivForeign(uint256 x_hi, uint256 x_lo, uint256 y) external pure {
        vm.assume(y != 0);
        uint512 memory x;
        x.from(x_hi, x_lo);
        (uint256 r_hi, uint256 r_lo) = tmp_uint512().odiv(x, y).into();
        (uint256 e_lo, uint256 e_hi) = SlowMath.fullDiv(x_lo, x_hi, y);
        assertEq(r_hi, e_hi);
        assertEq(r_lo, e_lo);
    }

    function test512Math_idivForeign(uint256 x_hi, uint256 x_lo, uint256 y) external pure {
        vm.assume(y != 0);
        (uint256 r_hi, uint256 r_lo) = tmp_uint512().from(x_hi, x_lo).idiv(y).into();
        (uint256 e_lo, uint256 e_hi) = SlowMath.fullDiv(x_lo, x_hi, y);
        assertEq(r_hi, e_hi);
        assertEq(r_lo, e_lo);
    }
}

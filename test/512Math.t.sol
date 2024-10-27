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
}

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

    // ======================= Square root tests =======================
    
    function test512Math_sqrtBasicCases() external pure {
        uint512 x = alloc();
        
        // Test zero
        x = x.from(0, 0);
        assertEq(x.sqrt(), 0, "sqrt(0) should be 0");
        
        // Test small values
        x = x.from(0, 1);
        assertEq(x.sqrt(), 1, "sqrt(1) should be 1");
        
        x = x.from(0, 4);
        assertEq(x.sqrt(), 2, "sqrt(4) should be 2");
        
        x = x.from(0, 16);
        assertEq(x.sqrt(), 4, "sqrt(16) should be 4");
        
        // Test powers of 2
        x = x.from(0, 1 << 64);
        assertEq(x.sqrt(), 1 << 32, "sqrt(2^64) should be 2^32");
        
        x = x.from(0, 1 << 128);
        assertEq(x.sqrt(), 1 << 64, "sqrt(2^128) should be 2^64");
        
        x = x.from(1, 0);
        assertEq(x.sqrt(), 1 << 128, "sqrt(2^256) should be 2^128");
        
        x = x.from(1 << 64, 0);
        assertEq(x.sqrt(), 1 << 160, "sqrt(2^320) should be 2^160");
    }
    
    function test512Math_sqrtEdgeCases() external pure {
        uint512 x = alloc();
        
        // Test maximum values
        x = x.from(0, type(uint256).max);
        assertEq(x.sqrt(), 0xffffffffffffffffffffffffffffffff, "sqrt(2^256-1) should be correct");
        
        // Test specific edge case from previous testing
        x = x.from(1, type(uint256).max);
        assertEq(x.sqrt(), 0x100000000000000000000000000000000, "sqrt(2^256 + 2^256-1) should be correct");
        
        // Test maximum result case
        x = x.from(type(uint256).max, type(uint256).max);
        assertEq(x.sqrt(), type(uint256).max, "sqrt of max 512-bit should be max uint256");
        
        // Test boundary case (2^256-1)^2
        x = x.from(
            0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe,
            1
        );
        assertEq(x.sqrt(), type(uint256).max, "sqrt((2^256-1)^2) should be 2^256-1");
    }
    
    function test512Math_sqrtSpecificFailingCases() external pure {
        uint512 x = alloc();
        
        // Test case that previously failed: (519, 2055)
        x = x.from(519, 2055);
        uint256 result = x.sqrt();
        
        // Verify the result
        (uint256 r2_hi, uint256 r2_lo) = mul512(result, result);
        bool resultSquaredFits = (r2_hi < 519) || (r2_hi == 519 && r2_lo <= 2055);
        assertTrue(resultSquaredFits, "result^2 should be <= input for (519, 2055)");
        
        if (result < type(uint256).max) {
            uint256 resultPlus1 = result + 1;
            (uint256 r2p1_hi, uint256 r2p1_lo) = mul512(resultPlus1, resultPlus1);
            bool resultPlus1SquaredExceeds = (r2p1_hi > 519) || (r2p1_hi == 519 && r2p1_lo > 2055);
            assertTrue(resultPlus1SquaredExceeds, "(result+1)^2 should be > input for (519, 2055)");
        }
        
        // Test odd power cases
        uint256[10] memory oddPowers = [
            uint256(1), 3, 7, 15, 31, 63, 127, 255, 511, 1023
        ];
        
        for (uint256 i = 0; i < oddPowers.length; i++) {
            x = x.from(oddPowers[i], type(uint256).max);
            result = x.sqrt();
            
            (r2_hi, r2_lo) = mul512(result, result);
            bool oddPowerResultSquaredFits = (r2_hi < oddPowers[i]) || 
                               (r2_hi == oddPowers[i] && r2_lo <= type(uint256).max);
            assertTrue(oddPowerResultSquaredFits, "result^2 should be <= input for odd power case");
        }
    }
    
    function testFuzz512Math_sqrt(uint256 hi, uint256 lo) external pure {
        uint512 x = alloc();
        x = x.from(hi, lo);
        
        uint256 result = x.sqrt();
        
        // Check: result^2 <= (hi:lo)
        (uint256 r2_hi, uint256 r2_lo) = mul512(result, result);
        bool resultSquaredFits = (r2_hi < hi) || (r2_hi == hi && r2_lo <= lo);
        assertTrue(resultSquaredFits, "result^2 should be <= input");
        
        // Check: (result+1)^2 > (hi:lo) for inputs where sqrt < 2^256
        if (result == type(uint256).max) {
            // For max result, verify input requires it
            bool inputRequiresMaxResult = hi > 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe || 
                                         (hi == 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe && lo >= 1);
            assertTrue(inputRequiresMaxResult, "max result should only occur for inputs >= (2^256-1)^2");
        } else {
            uint256 resultPlus1 = result + 1;
            (uint256 r2p1_hi, uint256 r2p1_lo) = mul512(resultPlus1, resultPlus1);
            bool resultPlus1SquaredExceeds = (r2p1_hi > hi) || (r2p1_hi == hi && r2p1_lo > lo);
            assertTrue(resultPlus1SquaredExceeds, "(result+1)^2 should be > input");
        }
    }
    
    // Helper function for 256x256 multiplication using SlowMath
    function mul512(uint256 a, uint256 b) internal pure returns (uint256 hi, uint256 lo) {
        (lo, hi) = SlowMath.fullMul(a, b);
    }
}

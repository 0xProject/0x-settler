// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {uint512, alloc} from "src/utils/512Math.sol";
import {SlowMath} from "./SlowMath.sol";
import {Test} from "@forge-std/Test.sol";

contract SqrtOverrideTest is Test {
    function test_seed_430_should_fail() public pure {
        uint256 x_hi = 0x000000000000000000000000000000000000000580398dae536e7fe242efe66a;
        uint256 x_lo = 0x0000000000000000001d9ad7c2a7ff6112e8bfd6cb5a1057f01519d7623fbd4a;

        uint512 x = alloc().from(x_hi, x_lo);
        uint256 r = x.sqrt(44, 430);

        // With seed 430, we get ...906 which is too high
        // r^2 > x, so this should fail
        (uint256 r2_lo, uint256 r2_hi) = SlowMath.fullMul(r, r);
        bool is_valid = (r2_hi < x_hi) || (r2_hi == x_hi && r2_lo <= x_lo);

        assertTrue(!is_valid, "Seed 430 should produce invalid result");
    }

    function test_seed_434_should_work() public pure {
        uint256 x_hi = 0x000000000000000000000000000000000000000580398dae536e7fe242efe66a;
        uint256 x_lo = 0x0000000000000000001d9ad7c2a7ff6112e8bfd6cb5a1057f01519d7623fbd4a;

        uint512 x = alloc().from(x_hi, x_lo);
        uint256 r = x.sqrt(44, 434);

        // With seed 434, we get ...905 which is correct
        // r^2 <= x < (r+1)^2
        (uint256 r2_lo, uint256 r2_hi) = SlowMath.fullMul(r, r);
        bool lower_ok = (r2_hi < x_hi) || (r2_hi == x_hi && r2_lo <= x_lo);

        assertTrue(lower_ok, "r^2 should be <= x");

        if (r < type(uint256).max) {
            uint256 r1 = r + 1;
            (uint256 r1_2_lo, uint256 r1_2_hi) = SlowMath.fullMul(r1, r1);
            bool upper_ok = (r1_2_hi > x_hi) || (r1_2_hi == x_hi && r1_2_lo > x_lo);
            assertTrue(upper_ok, "(r+1)^2 should be > x");
        }
    }

    function test_seed_436_should_work() public pure {
        uint256 x_hi = 0x000000000000000000000000000000000000000580398dae536e7fe242efe66a;
        uint256 x_lo = 0x0000000000000000001d9ad7c2a7ff6112e8bfd6cb5a1057f01519d7623fbd4a;

        uint512 x = alloc().from(x_hi, x_lo);
        uint256 r = x.sqrt(44, 436);

        // With seed 436, we get ...905 which is correct
        // r^2 <= x < (r+1)^2
        (uint256 r2_lo, uint256 r2_hi) = SlowMath.fullMul(r, r);
        bool lower_ok = (r2_hi < x_hi) || (r2_hi == x_hi && r2_lo <= x_lo);

        assertTrue(lower_ok, "r^2 should be <= x");

        if (r < type(uint256).max) {
            uint256 r1 = r + 1;
            (uint256 r1_2_lo, uint256 r1_2_hi) = SlowMath.fullMul(r1, r1);
            bool upper_ok = (r1_2_hi > x_hi) || (r1_2_hi == x_hi && r1_2_lo > x_lo);
            assertTrue(upper_ok, "(r+1)^2 should be > x");
        }
    }
}
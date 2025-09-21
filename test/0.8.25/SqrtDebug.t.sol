// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {uint512, alloc, tmp} from "src/utils/512Math.sol";
import {SlowMath} from "./SlowMath.sol";
import {Test} from "@forge-std/Test.sol";

contract SqrtDebugTest is Test {
    function test_specific_failing_inputs() external pure {
        uint256 x_hi = 0x000000000000000000000000000000000000000580398dae536e7fe242efe66a;
        uint256 x_lo = 0x0000000000000000001d9ad7c2a7ff6112e8bfd6cb5a1057f01519d7623fbd4a;

        uint512 x = alloc().from(x_hi, x_lo);
        uint256 r = x.sqrt();

        // Check that r^2 <= x < (r+1)^2
        (uint256 r2_lo, uint256 r2_hi) = SlowMath.fullMul(r, r);
        assertTrue((r2_hi < x_hi) || (r2_hi == x_hi && r2_lo <= x_lo), "sqrt too high");

        if (r < type(uint256).max) {
            uint256 r1 = r + 1;
            (uint256 r1_2_lo, uint256 r1_2_hi) = SlowMath.fullMul(r1, r1);
            assertTrue((r1_2_hi > x_hi) || (r1_2_hi == x_hi && r1_2_lo > x_lo), "sqrt too low");
        }
    }
}
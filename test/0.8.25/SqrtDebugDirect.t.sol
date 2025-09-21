// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {uint512, alloc} from "src/utils/512Math.sol";
import {SlowMath} from "./SlowMath.sol";
import {Test} from "@forge-std/Test.sol";
import {console} from "@forge-std/console.sol";

contract SqrtDebugDirectTest is Test {
    // The known failing input
    uint256 constant X_HI = 0x000000000000000000000000000000000000000580398dae536e7fe242efe66a;
    uint256 constant X_LO = 0x0000000000000000001d9ad7c2a7ff6112e8bfd6cb5a1057f01519d7623fbd4a;

    function test_direct_with_override() public view {
        uint512 x = alloc().from(X_HI, X_LO);

        // Test with seed 430 (should fail)
        console.log("Testing seed 430:");
        uint256 r430 = x.sqrt(44, 430);
        console.log("  Result:", r430);

        // Test with seed 434 (original)
        console.log("Testing seed 434:");
        uint256 r434 = x.sqrt(44, 434);
        console.log("  Result:", r434);

        // Test with seed 436
        console.log("Testing seed 436:");
        uint256 r436 = x.sqrt(44, 436);
        console.log("  Result:", r436);

        // Test without override (use natural lookup)
        console.log("Testing without override (bucket 999):");
        uint256 r_natural = x.sqrt(999, 0);
        console.log("  Result:", r_natural);

        // Check correctness
        (uint256 r2_lo, uint256 r2_hi) = SlowMath.fullMul(r434, r434);
        console.log("r434^2 hi:", r2_hi);
        console.log("r434^2 lo:", r2_lo);
        console.log("x_hi:     ", X_HI);
        console.log("x_lo:     ", X_LO);

        bool r434_ok = (r2_hi < X_HI) || (r2_hi == X_HI && r2_lo <= X_LO);
        console.log("r434 is valid lower bound:", r434_ok ? uint256(1) : uint256(0));

        if (r434 < type(uint256).max) {
            uint256 r434_plus = r434 + 1;
            (uint256 rp2_lo, uint256 rp2_hi) = SlowMath.fullMul(r434_plus, r434_plus);
            bool r434_upper_ok = (rp2_hi > X_HI) || (rp2_hi == X_HI && rp2_lo > X_LO);
            console.log("r434+1 is valid upper bound:", r434_upper_ok ? uint256(1) : uint256(0));
        }
    }
}
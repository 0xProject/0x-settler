// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test, console2} from "@forge-std/Test.sol";
import {uint512, alloc, Lib512MathAccessors, Lib512MathArithmetic} from "../../src/utils/512Math.sol";

/// Debugging harness: call lnQ256 and compare against expected values
contract LnQ256Debug is Test {
    using Lib512MathAccessors for uint512;
    using Lib512MathArithmetic for uint512;

    function test_debug_largePrime() public view {
        // x = 2^255 - 19
        uint512 x = alloc().from(0, 57896044618658097711785492504343953926634992332820282019728792003956564819949);
        uint256 gasBefore = gasleft();
        uint512 r = x.lnQ256();
        uint256 gasUsed = gasBefore - gasleft();
        (uint256 hi, uint256 lo) = r.into();
        console2.log("x=2^255-19: hi =", hi);
        console2.log("x=2^255-19: lo =", lo);
        console2.log("gas used =", gasUsed);
        console2.log("expected hi = 176");
        console2.log("expected lo = 87137141660133365321152211079996203992102939802697113616796428489378212295061");
    }

    function test_debug_max() public view {
        uint512 x = alloc().from(type(uint256).max, type(uint256).max);
        uint256 gasBefore = gasleft();
        uint512 r = x.lnQ256();
        uint256 gasUsed = gasBefore - gasleft();
        (uint256 hi, uint256 lo) = r.into();
        console2.log("x=max: hi =", hi);
        console2.log("x=max: lo =", lo);
        console2.log("gas used =", gasUsed);
        console2.log("expected hi = 354");
        console2.log("expected lo = 103212025217616957519630260555236733345647245497292992366923423973770079262671");
    }
}

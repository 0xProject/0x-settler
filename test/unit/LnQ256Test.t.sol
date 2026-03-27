// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "@forge-std/Test.sol";
import {uint512, alloc, Lib512MathAccessors, Lib512MathArithmetic} from "../../src/utils/512Math.sol";

contract LnQ256Test is Test {
    using Lib512MathAccessors for uint512;
    using Lib512MathArithmetic for uint512;

    function _ln(uint256 x_hi, uint256 x_lo) internal pure returns (uint256, uint256) {
        uint512 x = alloc().from(x_hi, x_lo);
        uint512 r = x.lnQ256();
        return r.into();
    }

    // Smoke tests: values from the Python model
    function test_lnQ256_x1() public pure {
        (uint256 hi, uint256 lo) = _ln(0, 1);
        assertEq(hi, 0, "x=1 hi");
        assertEq(lo, 0, "x=1 lo");
    }

    function test_lnQ256_x2() public pure {
        (uint256 hi, uint256 lo) = _ln(0, 2);
        assertEq(hi, 0, "x=2 hi");
        assertEq(lo, 80260960185991308862233904206310070533990667611589946606122867505419956976171, "x=2 lo");
    }

    function test_lnQ256_x3() public pure {
        (uint256 hi, uint256 lo) = _ln(0, 3);
        assertEq(hi, 1, "x=3 hi");
        assertEq(lo, 11418522929353742016527484700215317765135896538862575624148025318121769874828, "x=3 lo");
    }

    function test_lnQ256_x7() public pure {
        (uint256 hi, uint256 lo) = _ln(0, 7);
        assertEq(hi, 1, "x=7 hi");
        assertEq(lo, 109528912389895901933993050910717077243425093389684305998407190592912499327546, "x=7 lo");
    }

    function test_lnQ256_x8() public pure {
        (uint256 hi, uint256 lo) = _ln(0, 8);
        assertEq(hi, 2, "x=8 hi");
        assertEq(lo, 9198702083341535739559742601554395895432033503488711739453434500433611648643, "x=8 lo");
    }

    function test_lnQ256_x9() public pure {
        (uint256 hi, uint256 lo) = _ln(0, 9);
        assertEq(hi, 2, "x=9 hi");
        assertEq(lo, 22837045858707484033054969400430635530271793077725151248296050636243539749657, "x=9 lo");
    }

    // x = 2^255 - 19
    function test_lnQ256_largePrime() public pure {
        (uint256 hi, uint256 lo) = _ln(0, 57896044618658097711785492504343953926634992332820282019728792003956564819949);
        assertEq(hi, 176, "x=2^255-19 hi");
        assertEq(lo, 87137141660133365321152211079996203992102939802697113616796428489378212295061, "x=2^255-19 lo");
    }

    // x = 2^255
    function test_lnQ256_pow2_255() public pure {
        (uint256 hi, uint256 lo) = _ln(0, 1 << 255);
        assertEq(hi, 176, "x=2^255 hi");
        assertEq(lo, 87137141660133365321152211079996203992102939802697113616796428489378212295099, "x=2^255 lo");
    }

    // x = 2^512 - 1 (max value)
    function test_lnQ256_max() public pure {
        (uint256 hi, uint256 lo) = _ln(type(uint256).max, type(uint256).max);
        assertEq(hi, 354, "x=max hi");
        assertEq(lo, 103212025217616957519630260555236733345647245497292992366923423973770079262671, "x=max lo");
    }

    // x = 0 should revert
    function test_lnQ256_zero_reverts() public {
        vm.expectRevert();
        this.externalLnQ256(0, 0);
    }

    function externalLnQ256(uint256 hi, uint256 lo) external pure returns (uint256, uint256) {
        uint512 x = alloc().from(hi, lo);
        uint512 r = x.lnQ256();
        return r.into();
    }
}

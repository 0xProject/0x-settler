// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "@forge-std/Test.sol";
import {uint512, alloc, Lib512MathAccessors, Lib512MathArithmetic} from "../../src/utils/512Math.sol";

/// @dev Differential fuzz test for the relaxed lnQ256 lower/upper bound functions.
/// Requires: python3 with mpmath installed.
/// Run: forge test --match-contract LnQ256BoundsFuzzTest --ffi
contract LnQ256BoundsFuzzTest is Test {
    using Lib512MathAccessors for uint512;
    using Lib512MathArithmetic for uint512;

    string private constant _SCRIPT = "test/0.8.25/lnq256_bounds_ffi.py";

    function _oracle(uint256 x_hi, uint256 x_lo)
        internal
        returns (uint256 floor_hi, uint256 floor_lo, uint256 ceil_hi, uint256 ceil_lo)
    {
        string[] memory args = new string[](4);
        args[0] = "python3";
        args[1] = _SCRIPT;
        args[2] = vm.toString(bytes32(x_hi));
        args[3] = vm.toString(bytes32(x_lo));
        bytes memory result = vm.ffi(args);
        return abi.decode(result, (uint256, uint256, uint256, uint256));
    }

    function _lower(uint256 x_hi, uint256 x_lo) internal pure returns (uint256 r_hi, uint256 r_lo) {
        uint512 x = alloc().from(x_hi, x_lo);
        uint512 r = x.lnQ256LowerBound();
        return r.into();
    }

    function _upper(uint256 x_hi, uint256 x_lo) internal pure returns (uint256 r_hi, uint256 r_lo) {
        uint512 x = alloc().from(x_hi, x_lo);
        uint512 r = x.lnQ256UpperBound();
        return r.into();
    }

    function _inc(uint256 x_hi, uint256 x_lo) internal pure returns (uint256 r_hi, uint256 r_lo) {
        assembly ("memory-safe") {
            r_lo := add(x_lo, 1)
            r_hi := add(x_hi, iszero(r_lo))
        }
    }

    function _assertLowerOk(
        uint256 actual_hi,
        uint256 actual_lo,
        uint256 floor_hi,
        uint256 floor_lo
    ) internal pure {
        if (actual_hi == floor_hi && actual_lo == floor_lo) {
            return;
        }
        (uint256 inc_hi, uint256 inc_lo) = _inc(actual_hi, actual_lo);
        assertEq(inc_hi, floor_hi, "lower hi mismatch");
        assertEq(inc_lo, floor_lo, "lower lo mismatch");
    }

    function _assertUpperOk(
        uint256 actual_hi,
        uint256 actual_lo,
        uint256 ceil_hi,
        uint256 ceil_lo
    ) internal pure {
        if (actual_hi == ceil_hi && actual_lo == ceil_lo) {
            return;
        }
        (uint256 next_hi, uint256 next_lo) = _inc(ceil_hi, ceil_lo);
        assertEq(actual_hi, next_hi, "upper hi mismatch");
        assertEq(actual_lo, next_lo, "upper lo mismatch");
    }

    function test_lnQ256Bounds_regression_q218_randomWitness() public {
        uint256 x_hi = 0x74285ee8e7fa528d0aab5961eb23471830aaac7ddbc4eae1a0d3320752bbe5e5;
        uint256 x_lo = 0xbf33f451638c6919750bf44234f5450a3acc1482cbe4af77ded5c915058eda8d;

        (uint256 floor_hi, uint256 floor_lo, uint256 ceil_hi, uint256 ceil_lo) = _oracle(x_hi, x_lo);
        (uint256 lower_hi, uint256 lower_lo) = _lower(x_hi, x_lo);
        (uint256 upper_hi, uint256 upper_lo) = _upper(x_hi, x_lo);

        _assertLowerOk(lower_hi, lower_lo, floor_hi, floor_lo);
        _assertUpperOk(upper_hi, upper_lo, ceil_hi, ceil_lo);
    }

    function testFuzz_lnQ256Bounds_diff(uint256 x_hi, uint256 x_lo) external {
        if (x_hi == 0 && x_lo == 0) {
            x_lo = 1;
        }

        (uint256 floor_hi, uint256 floor_lo, uint256 ceil_hi, uint256 ceil_lo) = _oracle(x_hi, x_lo);
        (uint256 lower_hi, uint256 lower_lo) = _lower(x_hi, x_lo);
        (uint256 upper_hi, uint256 upper_lo) = _upper(x_hi, x_lo);

        _assertLowerOk(lower_hi, lower_lo, floor_hi, floor_lo);
        _assertUpperOk(upper_hi, upper_lo, ceil_hi, ceil_lo);
    }
}

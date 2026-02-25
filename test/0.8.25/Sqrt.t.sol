// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Sqrt} from "src/vendor/Sqrt.sol";
import {Test} from "@forge-std/Test.sol";

contract SqrtTest is Test {
    using Sqrt for uint256;

    uint256 private constant _SQRT_FLOOR_MAX_UINT256 = type(uint128).max;
    uint256 private constant _SQRT_CEIL_MAX_UINT256 = uint256(1) << 128;
    uint256 private constant _SQRT_FLOOR_MAX_UINT256_SQUARED =
        0xfffffffffffffffffffffffffffffffe00000000000000000000000000000001;

    function testSqrtUp_overflowSquareRange(uint256 x) external pure {
        x = bound(x, _SQRT_FLOOR_MAX_UINT256_SQUARED + 1, type(uint256).max);

        assertEq(x.sqrt(), _SQRT_FLOOR_MAX_UINT256, "sqrt overflow-square range");
        assertEq(x.sqrtUp(), _SQRT_CEIL_MAX_UINT256, "sqrtUp overflow-square range");
    }

    function testSqrtUp_overflowSquareBoundary() external pure {
        uint256 x = _SQRT_FLOOR_MAX_UINT256_SQUARED;

        assertEq(x.sqrt(), _SQRT_FLOOR_MAX_UINT256, "sqrt boundary");
        assertEq(x.sqrtUp(), _SQRT_FLOOR_MAX_UINT256, "sqrtUp boundary");
    }
}

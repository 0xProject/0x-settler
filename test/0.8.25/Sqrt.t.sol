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

    function _sqrtFloor(uint256 x) internal virtual returns (uint256) {
        return x.sqrt();
    }

    function _sqrtUp(uint256 x) internal virtual returns (uint256) {
        return x.sqrtUp();
    }

    function testSqrt(uint256 x) external {
        uint256 r = _sqrtFloor(x);
        assertLe(r * r, x, "sqrt too high");
        if (x < _SQRT_FLOOR_MAX_UINT256_SQUARED) {
            r++;
            assertGt(r * r, x, "sqrt too low");
        } else {
            assertEq(r, _SQRT_FLOOR_MAX_UINT256, "sqrt overflow");
        }
    }

    function testSqrtUp(uint256 x) external {
        uint256 r = _sqrtUp(x);
        if (x <= _SQRT_FLOOR_MAX_UINT256_SQUARED) {
            assertGe(r * r, x, "sqrtUp too low");
        } else {
            assertEq(r, _SQRT_CEIL_MAX_UINT256, "sqrtUp overflow");
        }
        if (x != 0) {
            r--;
            assertLt(r * r, x, "sqrtUp too high");
        } else {
            assertEq(r, 0, "sqrtUp underflow");
        }
    }

    function testSqrtUp_overflowSquareRange(uint256 x) external {
        x = bound(x, _SQRT_FLOOR_MAX_UINT256_SQUARED + 1, type(uint256).max);

        assertEq(_sqrtFloor(x), _SQRT_FLOOR_MAX_UINT256, "sqrt overflow-square range");
        assertEq(_sqrtUp(x), _SQRT_CEIL_MAX_UINT256, "sqrtUp overflow-square range");
    }

    function testSqrtUp_overflowSquareBoundary() external {
        uint256 x = _SQRT_FLOOR_MAX_UINT256_SQUARED;

        assertEq(_sqrtFloor(x), _SQRT_FLOOR_MAX_UINT256, "sqrt boundary");
        assertEq(_sqrtUp(x), _SQRT_FLOOR_MAX_UINT256, "sqrtUp boundary");
    }
}

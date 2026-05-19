// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Cbrt} from "src/vendor/Cbrt.sol";
import {Test} from "@forge-std/Test.sol";

contract CbrtTest is Test {
    using Cbrt for uint256;

    uint256 private constant _CBRT_FLOOR_MAX_UINT256 = 0x285145f31ae515c447bb56;
    uint256 private constant _CBRT_CEIL_MAX_UINT256 = 0x285145f31ae515c447bb57;
    uint256 private constant _CBRT_FLOOR_MAX_UINT256_CUBE =
        0xffffffffffffffffffffef214b5539a2d22f71387253e480168f34c9da3f5898;

    function _cbrtFloor(uint256 x) internal virtual returns (uint256) {
        return x.cbrt();
    }

    function _cbrtUp(uint256 x) internal virtual returns (uint256) {
        return x.cbrtUp();
    }

    function testCbrt(uint256 x) external {
        uint256 r = _cbrtFloor(x);
        assertLe(r * r * r, x, "cbrt too high");
        if (x < _CBRT_FLOOR_MAX_UINT256_CUBE) {
            r++;
            assertGt(r * r * r, x, "cbrt too low");
        } else {
            assertEq(r, _CBRT_FLOOR_MAX_UINT256, "cbrt overflow");
        }
    }

    function testCbrtUp(uint256 x) external {
        uint256 r = _cbrtUp(x);
        if (x <= _CBRT_FLOOR_MAX_UINT256_CUBE) {
            assertGe(r * r * r, x, "cbrtUp too low");
        } else {
            assertEq(r, _CBRT_CEIL_MAX_UINT256, "cbrtUp overflow");
        }
        if (x != 0) {
            r--;
            assertLt(r * r * r, x, "cbrtUp too high");
        } else {
            assertEq(r, 0, "cbrtUp underflow");
        }
    }

    function testCbrtUp_overflowCubeRange(uint256 x) external {
        x = bound(x, _CBRT_FLOOR_MAX_UINT256_CUBE + 1, type(uint256).max);

        assertEq(_cbrtFloor(x), _CBRT_FLOOR_MAX_UINT256, "cbrt overflow-cube range");
        assertEq(_cbrtUp(x), _CBRT_CEIL_MAX_UINT256, "cbrtUp overflow-cube range");
    }

    function testCbrtUp_overflowCubeBoundary() external {
        uint256 x = _CBRT_FLOOR_MAX_UINT256_CUBE;

        assertEq(_cbrtFloor(x), _CBRT_FLOOR_MAX_UINT256, "cbrt boundary");
        assertEq(_cbrtUp(x), _CBRT_FLOOR_MAX_UINT256, "cbrtUp boundary");
    }
}

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

    function testCbrtUp_overflowCubeRange(uint256 x) external pure {
        x = bound(x, _CBRT_FLOOR_MAX_UINT256_CUBE + 1, type(uint256).max);

        assertEq(x.cbrt(), _CBRT_FLOOR_MAX_UINT256, "cbrt overflow-cube range");
        assertEq(x.cbrtUp(), _CBRT_CEIL_MAX_UINT256, "cbrtUp overflow-cube range");
    }

    function testCbrtUp_overflowCubeBoundary() external pure {
        uint256 x = _CBRT_FLOOR_MAX_UINT256_CUBE;

        assertEq(x.cbrt(), _CBRT_FLOOR_MAX_UINT256, "cbrt boundary");
        assertEq(x.cbrtUp(), _CBRT_FLOOR_MAX_UINT256, "cbrtUp boundary");
    }
}

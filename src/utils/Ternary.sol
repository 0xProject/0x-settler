// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

library Ternary {
    function ternary(bool c, uint256 x, uint256 y) internal pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := xor(y, mul(xor(x, y), c))
        }
    }

    function ternary(bool c, int256 x, int256 y) internal pure returns (int256 r) {
        assembly ("memory-safe") {
            r := xor(y, mul(xor(x, y), c))
        }
    }

    function maybeSwap(bool c, uint256 x, uint256 y) internal pure returns (uint256 a, uint256 b) {
        assembly ("memory-safe") {
            let t := mul(xor(x, y), c)
            a := xor(x, t)
            b := xor(y, t)
        }
    }

    function maybeSwap(bool c, int256 x, int256 y) internal pure returns (int256 a, int256 b) {
        assembly ("memory-safe") {
            let t := mul(xor(x, y), c)
            a := xor(x, t)
            b := xor(y, t)
        }
    }
    
    function maybeSwap(bool c, IERC20 x, IERC20 y) internal pure returns (IERC20 a, IERC20 b) {
        (uint256 a_, uint256 b_) = maybeSwap(c, uint160(address(x)), uint160(address(y)));
        a = IERC20(address(uint160(a_)));
        b = IERC20(address(uint160(b_)));
    }
}

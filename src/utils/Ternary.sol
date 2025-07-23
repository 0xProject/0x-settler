// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

library Ternary {
    //// All the code duplication in this file is because solc isn't smart enough to figure out that
    //// it doesn't need to do a ton of masking when types are cast to each other without
    //// modification.

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

    function ternary(bool c, bytes4 x, bytes4 y) internal pure returns (bytes4 r) {
        assembly ("memory-safe") {
            r := xor(y, mul(xor(x, y), c))
        }
    }

    function ternary(bool c, address x, address y) internal pure returns (address r) {
        assembly ("memory-safe") {
            r := xor(y, mul(xor(x, y), c))
        }
    }

    function orZero(bool c, uint256 x) internal pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := mul(x, c)
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
        assembly ("memory-safe") {
            let t := mul(xor(x, y), c)
            a := xor(x, t)
            b := xor(y, t)
        }
    }

    function maybeSwap(bool c, address x, address y) internal pure returns (address a, address b) {
        assembly ("memory-safe") {
            let t := mul(xor(x, y), c)
            a := xor(x, t)
            b := xor(y, t)
        }
    }
}

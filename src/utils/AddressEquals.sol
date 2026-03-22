// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

library AddressEquals {
    function eq(address a, address b) internal pure returns (bool c) {
        assembly ("memory-safe") {
            c := iszero(shl(0x60, xor(a, b)))
        }
    }

    function eq(IERC20 a, IERC20 b) internal pure returns (bool) {
        return eq(address(a), address(b));
    }
}

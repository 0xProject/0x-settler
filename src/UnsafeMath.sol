// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

library UnsafeMath {
    function unsafeInc(uint256 i) internal pure returns (uint256) {
        unchecked {
            return i + 1;
        }
    }
}

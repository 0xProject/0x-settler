// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

library Clz {
    /// @dev Count leading zeros.
    /// Returns the number of zeros preceding the most significant one bit.
    /// If `x` is zero, returns 256.
    function clz(uint256 x) internal pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := clz(x)
        }
    }

    function bitLength(uint256 x) internal pure returns (uint256) {
        unchecked {
            return 256 - clz(x);
        }
    }
}

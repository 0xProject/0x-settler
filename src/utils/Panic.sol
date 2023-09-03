// SPDX-License-Identifier: MIT
pragma solidity 0.8.21;

library Panic {
    function panic(uint256 code) internal pure {
        assembly ("memory-safe") {
            mstore(0x00, 0x4e487b71) // selector for `Panic(uint256)`
            mstore(0x20, code)
            revert(0x1c, 0x24)
        }
    }
}

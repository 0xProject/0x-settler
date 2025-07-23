// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IDeployer} from "./IDeployer.sol";

library FastDeployer {
    function fastOwnerOf(IDeployer deployer, uint256 tokenId) internal view returns (address r) {
        assembly ("memory-safe") {
            mstore(0x00, 0x6352211e) // selector for `ownerOf(uint256)`
            mstore(0x20, tokenId)

            if iszero(staticcall(gas(), deployer, 0x1c, 0x24, 0x00, 0x20)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            if or(gt(0x20, returndatasize()), shr(0xa0, r)) { revert(0x00, 0x00) }
            r := mload(0x00)
        }
    }

    function fastPrev(IDeployer deployer, uint128 tokenId) internal view returns (address r) {
        assembly ("memory-safe") {
            mstore(0x10, tokenId)
            mstore(0x00, 0xe2603dc200000000000000000000000000000000) // selector for `prev(uint128)` with `tokenId`'s padding

            if iszero(staticcall(gas(), deployer, 0x0c, 0x24, 0x00, 0x20)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            if or(gt(0x20, returndatasize()), shr(0xa0, r)) { revert(0x00, 0x00) }
            r := mload(0x00)
        }
    }
}

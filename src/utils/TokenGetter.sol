// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

function fastGetToken(address pool, uint256 selector) view returns (IERC20 token) {
    // Scratch memory avoids allocating calldata and return buffers.
    // (bool success, bytes memory data) = pool.staticcall(abi.encodeWithSelector(bytes4(uint32(selector))));
    // if (!success) bubbleRevert(data);
    // token = abi.decode(data, (IERC20));
    assembly ("memory-safe") {
        mstore(0x00, selector)
        if iszero(staticcall(gas(), pool, 0x1c, 0x04, 0x00, 0x20)) {
            let ptr := mload(0x40)
            returndatacopy(ptr, 0x00, returndatasize())
            revert(ptr, returndatasize())
        }
        token := mload(0x00)
        if or(gt(0x20, returndatasize()), shr(0xa0, token)) { revert(0x00, 0x00) }
    }
}

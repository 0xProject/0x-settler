// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";

contract Relay {
    using SafeTransferLib for IERC20;

    event RelayAction(bytes32 requestId); // Graffiti for bridging operations through Relay

    function bridgeERC20ToRelay(IERC20 token, address to, bytes32 requestId) internal {
        emit RelayAction(requestId);

        uint256 amount = token.fastBalanceOf(address(this));
        assembly ("memory-safe") {
            let ptr := mload(0x40)

            mstore(0x54, requestId)
            mstore(0x34, amount)
            mstore(0x14, to)
            mstore(0x00, 0xa9059cbb000000000000000000000000) // selector for `transfer(address,uint256)` with `to`'s padding

            // Similar to SafeTransferLib.safeTransfer
            if iszero(call(gas(), token, 0x00, 0x10, 0x64, 0x00, 0x20)) {
                let ptr_ := mload(0x40)
                returndatacopy(ptr_, 0x00, returndatasize())
                revert(ptr_, returndatasize())
            }
            // We check that the call either returned exactly 1 [true] (can't just be non-zero
            // data), or had no return data.
            if iszero(or(and(eq(mload(0x00), 0x01), lt(0x1f, returndatasize())), iszero(returndatasize()))) {
                mstore(0x00, 0x90b8ec18) // Selector for `TransferFailed()`
                revert(0x1c, 0x04)
            }

            // restore clobbered memory
            mstore(0x40, ptr)
            mstore(0x60, 0x00)
        }
    }

    function bridgeNativeToRelay(address to, bytes32 requestId) internal {
        emit RelayAction(requestId);

        assembly ("memory-safe") {
            mstore(0x00, requestId)
            if iszero(call(gas(), to, selfbalance(), 0x00, 0x20, 0x00, 0x00)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
        }
    }
}

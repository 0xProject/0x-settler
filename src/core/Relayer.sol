// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";

contract Relayer {
    using SafeTransferLib for IERC20;

    event RelayerAction(); // Graffiti for bridging operations through Relayer

    function bridgeERC20ToRelayer(IERC20 token, address to, bytes32 requestId) internal {
        emit RelayerAction();

        uint256 amount = token.fastBalanceOf(address(this));
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(add(ptr, 0x54), requestId)
            mstore(add(ptr, 0x34), amount)
            mstore(add(ptr, 0x14), to)
            mstore(ptr, 0xa9059cbb000000000000000000000000) // selector for `transfer(address,uint256)` with `to`'s padding

            // Similar to SafeTransferLib.safeTransfer
            if iszero(call(gas(), token, 0x00, add(0x10, ptr), 0x64, 0x00, 0x20)) { 
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
        }
    }

    function bridgeNativeToRelayer(address to, bytes32 requestId) internal {
        emit RelayerAction();

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
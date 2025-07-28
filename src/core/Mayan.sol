// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";

contract Mayan {
    using SafeTransferLib for IERC20;

    function bridgeERC20ToMayan(address forwarder, bytes memory protocolAndData) internal {
        IERC20 token;
        assembly ("memory-safe") {
            // protocolData is abi.encode(mayanProtocol, protocolData)
            // and protocolData is (4 bytes selector, 32 bytes token, 32 bytes amount, ...anything else)
            // then, token is at 0x84
            token := mload(add(0x84, protocolAndData))
        }

        uint256 amount = token.fastBalanceOf(address(this));
        token.safeApproveIfBelow(forwarder, amount);
        assembly ("memory-safe") {
            let ptr := mload(0x40)

            let size := mload(protocolAndData)
            mstore(add(0x14, ptr), token)
            // selector for `forwardERC20(address,uint256,(uint256,uint256,uint8,bytes32,bytes32),address,bytes)` with `token` padding
            mstore(ptr, 0xe4269fc4000000000000000000000000)
            mstore(add(0x34, ptr), amount)
            // permit data is not going to be used as we are approving forwarder.
            // As it is not used, then we can send anything we have in memory
            // which is most likely empty but might be dirty. Even if it is dirty,
            // permit's contents are not even verified so compiler will not complain.
            // Permit data is 0xa0 bytes long
            mcopy(add(0xf4, ptr), add(0x20, protocolAndData), size)
            // override protocolData offset to point to the start of the upcoming call calldata
            mstore(add(0x114, ptr), 0x120)
            // modify copied amount in protocolData which starts at 0x134
            // then, amountIn is at 0x178 after skipping size (0x20), selector (0x04) and token (0x20)
            mstore(add(0x178, ptr), amount)

            // `forwarder` is user provided and we don't check if it is a restricted target before calling it.
            // It is fine to do so as this block only calls `forwardERC20` so there is no arbitrary
            // execution and this selector doesn't collide with current restricted targets (AllowanceHolder & Permit2).
            if iszero(call(gas(), forwarder, 0x00, add(0x10, ptr), add(0xf4, size), 0x00, 0x00)) {
                let ptr_ := mload(0x40)
                returndatacopy(ptr_, 0x00, returndatasize())
                revert(ptr_, returndatasize())
            }
        }
    }

    function bridgeNativeToMayan(address forwarder, bytes memory protocolAndData) internal {
        assembly ("memory-safe") {
            let size := mload(protocolAndData)
            // temporarily clobber `protocolAndData` size memory area
            mstore(protocolAndData, 0xb0f584ff) // selector for `forwardEth(address,bytes)` with `mayanProtocol` padding

            // `forwarder` is user provided and we don't check if it is a restricted target before calling it.
            // It is fine to do so as this block only calls `forwardEth` so there is no arbitrary
            // execution and this selector doesn't collide with current restricted targets (AllowanceHolder & Permit2).
            if iszero(call(gas(), forwarder, selfbalance(), add(0x1c, protocolAndData), add(0x04, size), 0x00, 0x00)) {
                let ptr_ := mload(0x40)
                returndatacopy(ptr_, 0x00, returndatasize())
                revert(ptr_, returndatasize())
            }

            // restore clobbered memory
            mstore(protocolAndData, size)
        }
    }
}

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";

contract Mayan {
    using SafeTransferLib for IERC20;

    function bridgeERC20ToMayan(IERC20 token, address forwarder, address mayanProtocol, bytes memory protocolData) internal {
        uint256 amount = token.fastBalanceOf(address(this));
        token.safeApproveIfBelow(forwarder, amount);
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            
            let size := mload(protocolData)
            mcopy(add(0x134, ptr), protocolData, add(0x20, size))
            mstore(add(0x114, ptr), 0x120)
            mstore(add(0xf4, ptr), mayanProtocol)
            // permit data is not going to be used as we are approving forwarder.
            // As it is not used, then we can send anything we have in memory
            // which is most likely empty but might be dirty. Even if it is dirty,
            // permit's contents are not even verified so compiler will not complain.
            // Permit data is 0xa0 bytes long
            mstore(add(0x34, ptr), amount)
            mstore(add(0x14, ptr), token)
            // selector for `forwardERC20(address,uint256,(uint256,uint256,uint8,bytes32,bytes32),address,bytes)` with `token` padding
            mstore(ptr, 0xe4269fc4000000000000000000000000) 

            // modify copied amount in protocolData
            // protocolData is (4 bytes selector, 32 bytes token, 32 bytes amount, ...anything else)
            // it is stored at 0x134, so we need to skip size (0x20), selector (0x04) and token (0x20)
            mstore(add(0x178, ptr), amount)

            if iszero(call(gas(), forwarder, 0x0, add(0x10, ptr), add(0x144, size), 0x00, 0x00)) {
                let ptr_ := mload(0x40)
                returndatacopy(ptr_, 0x0, returndatasize())
                revert(ptr_, returndatasize())
            }
        }   
    }

    function bridgeNativeToMayan(address forwarder, address mayanProtocol, bytes memory protocolData) internal {
        assembly ("memory-safe") {
            let ptr := mload(0x40)

            let size := mload(protocolData)
            mcopy(add(0x54, ptr), protocolData, add(0x20, size))
            mstore(add(0x34, ptr), 0x40)
            mstore(add(0x14, ptr), mayanProtocol)
            mstore(ptr, 0xb0f584ff000000000000000000000000) // selector for `forwardEth(address,bytes)` with `mayanProtocol` padding

            // modify copied amount in protocolData
            // protocolData is (4 bytes selector, 32 bytes token, 32 bytes amount, ...anything else)
            // it is stored at 0x54, so we need to skip size (0x20), selector (0x04) and token (0x20)
            mstore(add(0x98, ptr), selfbalance())

            if iszero(call(gas(), forwarder, selfbalance(), add(0x10, ptr), add(0x64, size), 0x00, 0x00)) {
                let ptr_ := mload(0x40)
                returndatacopy(ptr_, 0x0, returndatasize())
                revert(ptr_, returndatasize())
            }
        }
    }
}
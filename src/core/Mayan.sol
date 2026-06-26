// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";

interface IMayanForwarder {
    struct PermitParams {
        uint256 value;
        uint256 deadline;
        uint8 v;
        bytes32 r;
        bytes32 s;
    }

    function forwardERC20(
        address tokenIn,
        uint256 amountIn,
        PermitParams calldata permitParams,
        address mayanProtocol,
        bytes calldata protocolData
    ) external payable;

    function forwardEth(address mayanProtocol, bytes calldata protocolData) external payable;
}

IMayanForwarder constant MAYAN_FORWARDER = IMayanForwarder(0x337685fdaB40D39bd02028545a4FfA7D287cC3E2);

contract Mayan {
    using SafeTransferLib for IERC20;

    /// @notice Bridge ERC20 tokens to Mayan
    /// @param protocolAndData ABI Encoding of (mayanProtocol, protocolData) arguments of `IMayanForwarder.forwardERC20`
    function bridgeERC20ToMayan(bytes memory protocolAndData) internal {
        IERC20 token;
        uint256 protocolDataPtr;
        assembly ("memory-safe") {
            // protocolAndData layout:
            // +0x00: length of protocolAndData
            // +0x20: mayanProtocol
            // +0x40: offset to protocolData
            let protocolAndDataPtr := add(0x20, protocolAndData)
            let protocolDataOffsetPtr := add(0x20, protocolAndDataPtr)
            let protocolDataOffset := mload(protocolDataOffsetPtr)
            protocolDataPtr := add(protocolDataOffset, protocolAndDataPtr)
            // Layout at `protocolDataPtr` is:
            // +0x00: length of protocolData
            // +0x20: selector to call in mayanProtocol (4 bytes)
            // +0x24: offset to tokenIn
            // +0x44: amountIn
            // ... anything else needed in the mayanProtocol call
            token := mload(add(0x24, protocolDataPtr))

            // override protocolDataOffset to point to the start of the upcoming `IMayanForwarder.forwardERC20` call
            // it will be pushed by:
            // - tokenIn (0x20 bytes)
            // - amountIn (0x20 bytes)
            // - permitParams (0xa0 bytes)
            mstore(protocolDataOffsetPtr, add(0xe0, protocolDataOffset))
        }
        IMayanForwarder forwarder = MAYAN_FORWARDER;
        uint256 amount = token.fastBalanceOf(address(this));
        token.safeApproveIfBelow(address(forwarder), amount);

        assembly ("memory-safe") {
            let ptr := mload(0x40)

            // update amountIn
            mstore(add(0x44, protocolDataPtr), amount)

            let size := mload(protocolAndData)
            mcopy(add(0xf4, ptr), add(0x20, protocolAndData), size)
            // permit data is not going to be used as we are approving forwarder.
            // As it is not used, then we can send anything we have in memory
            // which is most likely empty but might be dirty. Even if it is dirty,
            // permit's contents are not even verified so compiler will not complain.
            // Permit data is 0xa0 bytes long
            mstore(add(0x34, ptr), amount)
            mstore(add(0x14, ptr), token)
            mstore(ptr, 0xe4269fc4000000000000000000000000) // selector for `IMayanForwarder.forwardERC20` with `token` padding

            // `IMayanForwarder.forwardERC20` doesn't clash with restricted targets (AllowanceHolder & Permit2).
            // `forwarder` is also hardcoded to `MAYAN_FORWARDER`.
            if iszero(call(gas(), forwarder, 0x00, add(0x10, ptr), add(0xe4, size), 0x00, 0x00)) {
                let ptr_ := mload(0x40)
                returndatacopy(ptr_, 0x00, returndatasize())
                revert(ptr_, returndatasize())
            }
        }
    }

    /// @notice Bridge native tokens to Mayan
    /// @param protocolAndData Encoded call to `IMayanForwarder.forwardEth`
    function bridgeNativeToMayan(bytes memory protocolAndData) internal {
        IMayanForwarder forwarder = MAYAN_FORWARDER;
        assembly ("memory-safe") {
            let size := mload(protocolAndData)
            // temporarily clobber `protocolAndData` size memory area
            mstore(protocolAndData, 0xb0f584ff) // selector for `forwardEth(address,bytes)`

            // `IMayanForwarder.forwardEth` doesn't clash with restricted targets (AllowanceHolder & Permit2).
            // `forwarder` is also hardcoded to `MAYAN_FORWARDER`.
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

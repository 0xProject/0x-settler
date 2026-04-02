// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";

library fastLayerZeroOFT {
    function decimalConversionRate(address oft) internal view returns (uint256 conversionRate) {
        assembly ("memory-safe") {
            mstore(0x00, 0x963efcaa) // selector for `decimalConversionRate()`
            if iszero(staticcall(gas(), oft, 0x1c, 0x04, 0x00, 0x20)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            if gt(0x20, returndatasize()) { revert(0x00, 0x00) }
            conversionRate := mload(0x00)
        }
    }
}

contract LayerZeroOFT {
    using SafeTransferLib for IERC20;
    using fastLayerZeroOFT for address;

    IERC20 internal constant ETH = IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE);

    /// @notice Bridge via LayerZero
    /// @dev The sendData should be pre-encoded `send` arguments (without the selector).
    ///      This function will:
    ///      1. Get the full balance of the specified token
    ///      2. Approve the oft to spend the tokens
    ///      <<<< CONTINUE HERE >>>>
    ///      3. Update the amount in the tokenAmounts[0] of the EVM2AnyMessage
    ///      4. Call ccipSend with the entire native balance as value (for fee payment)
    ///
    ///      Expected sendData layout (ABI encoded):
    ///      - SendParam {
    ///          uint32 dstEid;        // Destination endpoint ID.
    ///          bytes32 to;           // Recipient address.
    ///          uint256 amountLD;     // Amount to send in local decimals.
    ///          uint256 minAmountLD;  // Minimum amount to send in local decimals.
    ///          bytes extraOptions;   // Additional options supplied by the caller to be used in the LayerZero message.
    ///          bytes composeMsg;     // The composed message for the send() operation.
    ///          bytes oftCmd;         // The OFT command to be executed, unused in default OFT implementations.
    ///      }
    ///      - struct MessagingFee {
    ///          uint256 nativeFee;
    ///          uint256 lzTokenFee;   // This one is unused in our implementation
    ///      }
    ///
    /// @param token The ERC20 token to bridge
    /// @param oft LayerZero OFT address
    /// @param sendData Pre-encoded `send` arguments (without selector)
    function bridgeLayerZeroOFT(IERC20 token, address oft, bytes memory sendData) internal {
        uint256 updatedInputAmount;
        uint256 nativeFee;

        // Get the native fee
        //
        // sendData layout:
        // 0x00: lenght of sendData
        // 0x20: offset to SendParam
        // 0x40: MessagingFee.nativeFee
        // 0x60: MessagingFee.lzTokenFee
        assembly ("memory-safe") {
            nativeFee := mload(add(0x40, sendData))
        }

        if (token == ETH) {
            uint256 value = address(this).balance;
            updatedInputAmount = value - nativeFee;

            // Update amount to match expected msg.value
            uint256 conversionRate = oft.decimalConversionRate();
            if (conversionRate > 1) {
                unchecked {
                    updatedInputAmount = (updatedInputAmount / conversionRate) * conversionRate;
                }
            }
            nativeFee += updatedInputAmount;
        } else {
            updatedInputAmount = token.fastBalanceOf(address(this));
            token.safeApproveIfBelow(oft, updatedInputAmount);
        }

        assembly ("memory-safe") {
            let sendDataPtr := add(0x20, sendData)
            let sendParamOffset := mload(sendDataPtr)
            let sendParamPtr := add(sendParamOffset, sendDataPtr)
            // sendParamPtr layout:
            // 0x00: dstEid
            // 0x20: to
            // 0x40: amountLD
            // 0x60: minAmountLD
            // 0x80: offset to extraOptions
            // 0xa0: offset to composeMsg
            // 0xc0: offset to oftCmd
            mstore(add(0x40, sendParamPtr), updatedInputAmount)

            let len := mload(sendData)
            // temporarily clobber `sendData` size memory area
            mstore(sendData, 0xc7c7f5b3) // selector for `send((uint32,bytes32,uint256,uint256,bytes,bytes,bytes),(uint256,uint256),address)`
            // `send` doesn't clash with any relevant function of restricted targets so we can skip checking oft
            if iszero(call(gas(), oft, nativeFee, add(0x1c, sendData), add(0x04, len), 0x00, 0x00)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            // restore clobbered memory
            mstore(sendData, len)
        }
    }
}

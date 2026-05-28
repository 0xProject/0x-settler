// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";

interface IOFT {
    event OFTSent(
        bytes32 indexed guid, uint32 dstEid, address indexed fromAddress, uint256 amountSentLD, uint256 amountReceivedLD
    );

    struct SendParam {
        uint32 dstEid;
        bytes32 to;
        uint256 amountLD;
        uint256 minAmountLD;
        bytes extraOptions;
        bytes composeMsg;
        bytes oftCmd;
    }

    struct MessagingFee {
        uint256 nativeFee;
        uint256 lzTokenFee;
    }

    struct OFTLimit {
        uint256 minAmountLD;
        uint256 maxAmountLD;
    }

    struct OFTReceipt {
        uint256 amountSentLD;
        uint256 amountReceivedLD;
    }

    struct OFTFeeDetail {
        int256 feeAmountLD;
        string description;
    }

    function send(SendParam memory sendParam, MessagingFee memory messagingFee, address refundAddress) external;

    function quoteOFT(SendParam calldata sendParam)
        external
        view
        returns (OFTLimit memory, OFTFeeDetail[] memory oftFeeDetails, OFTReceipt memory);

    function quoteSend(SendParam calldata sendParam, bool payInLzToken) external view returns (MessagingFee memory);
}

library FastLayerZeroOFT {
    function fastDecimalConversionRate(address oft) internal view returns (uint256 conversionRate) {
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

IERC20 constant ETH = IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE);

contract LayerZeroOFT {
    using SafeTransferLib for IERC20;
    using FastLayerZeroOFT for address;

    /// @notice Bridge via LayerZero
    /// @param token The ERC20 token to bridge
    /// @param oft LayerZero OFT address
    /// @param sendData Encoded call to `IOFT.send` without selector
    function bridgeLayerZeroOFT(IERC20 token, address oft, bytes memory sendData) internal {
        uint256 updatedInputAmount;
        uint256 nativeFee;

        // Get the native fee
        assembly ("memory-safe") {
            // sendData layout:
            // +0x00: length of sendData
            // +0x20: offset to SendParam
            // +0x40: MessagingFee.nativeFee
            // +0x60: MessagingFee.lzTokenFee
            nativeFee := mload(add(0x40, sendData))
        }

        if (token == ETH) {
            uint256 value = address(this).balance;
            updatedInputAmount = value - nativeFee;

            // Update amount to match expected msg.value
            uint256 conversionRate = oft.fastDecimalConversionRate();
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
            // Get the pointer to `sendParam` argument
            let sendDataPtr := add(0x20, sendData)
            let sendParamOffset := mload(sendDataPtr)
            let sendParamPtr := add(sendParamOffset, sendDataPtr)
            // `IOFT.SendParam` layout at `sendParamPtr`:
            // +0x00: dstEid
            // +0x20: to
            // +0x40: amountLD
            // ... all other `IOFT.SendParam` fields
            //
            // override amountLD
            mstore(add(0x40, sendParamPtr), updatedInputAmount)

            let len := mload(sendData)
            // temporarily clobber `sendData` size memory area
            mstore(sendData, 0xc7c7f5b3) // selector for `IOFT.send`
            // `oft` is user-provided but we're calling a specific function `IOFT.send`
            // which doesn't clash with restricted targets (AllowanceHolder & Permit2)
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

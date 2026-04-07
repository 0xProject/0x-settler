// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";

import {IOFT, ETH} from "src/core/LayerZeroOFT.sol";

interface IStargateV2 is IOFT {
    function sendToken(SendParam memory SendParam, MessagingFee memory messagingFee, address refundAddress) external;
}

contract StargateV2 {
    using SafeTransferLib for IERC20;

    /// @dev Bridge through StargateV2
    /// @param token The token to bridge
    /// @param pool The StargateV2 pool to bridge through
    /// @param sendData Encoded call to `sendToken` without selector
    function bridgeToStargateV2(IERC20 token, address pool, bytes memory sendData) internal {
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
            // Any excess on top of fee + amount is returned to
            // the refund address specified in `sendData`
            uint256 value = address(this).balance;
            // Input amount is adjusted with the pool convertRate
            // any leftover contributes towards the refunded excess
            updatedInputAmount = value - nativeFee;

            nativeFee += updatedInputAmount;
        } else {
            updatedInputAmount = token.fastBalanceOf(address(this));
            token.safeApproveIfBelow(pool, updatedInputAmount);
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
            mstore(sendData, 0xcbef2aa9) // selector for `IStargateV2.sendToken`
            // `pool` is user-provided but we're calling a specific function `IStargateV2.sendToken`
            // which doesn't clash with restricted targets (AllowanceHolder & Permit2)
            if iszero(call(gas(), pool, nativeFee, add(0x1c, sendData), add(0x04, len), 0x00, 0x00)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            // restore clobbered memory
            mstore(sendData, len)
        }
    }
}

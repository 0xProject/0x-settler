// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";

/// @dev Interface for CCIP Router
interface IRouterClient {
    struct EVMTokenAmount {
        address token;
        uint256 amount;
    }

    struct EVM2AnyMessage {
        bytes receiver;
        bytes data;
        EVMTokenAmount[] tokenAmounts;
        address feeToken;
        bytes extraArgs;
    }

    function ccipSend(uint64 destinationChainSelector, EVM2AnyMessage calldata message)
        external
        payable
        returns (bytes32);

    function getFee(uint64 destinationChainSelector, EVM2AnyMessage calldata message) external view returns (uint256);

    function isChainSupported(uint64 chainSelector) external view returns (bool);
}

interface IOnRamp {
    /// @dev Matches Internal.EVM2EVMMessage from the CCIP onRamp for event decoding
    struct EVM2EVMMessage {
        uint64 sourceChainSelector;
        address sender;
        address receiver;
        uint64 sequenceNumber;
        uint256 gasLimit;
        bool strict;
        uint64 nonce;
        address feeToken;
        uint256 feeTokenAmount;
        bytes data;
        IRouterClient.EVMTokenAmount[] tokenAmounts;
        bytes[] sourceTokenData;
        bytes32 messageId;
    }
}

/// @title CCIP
/// @notice Chainlink CCIP bridge integration for BridgeSettler
/// @dev Handles ERC20 token bridging via CCIP with native token fee payment
contract CCIP {
    using SafeTransferLib for IERC20;

    /// @notice Bridge ERC20 tokens via CCIP, paying fees in native token
    /// @param router The CCIP router address
    /// @param ccipSendData Encoded call to `IRouterClient.ccipSend` without selector
    function bridgeToCCIP(address router, bytes memory ccipSendData) internal {
        IERC20 token;
        uint256 tokenAmountsPtr;

        // Check ccipSendData and get the bridged token
        assembly ("memory-safe") {
            // ccipSendData layout:
            // +0x00: ccipSendData length
            // +0x20: destinationChainSelector
            // +0x40: offset to IRouterClient.EVM2AnyMessage
            let dataStart := add(0x20, ccipSendData) // skip bytes length
            // Malformed offsets are treated as GIGO errors. If they don't result in an OOG/OOM
            // error, they might affect token detection and amount override, which will result in
            // a malformed call to CCIP and most likely a revert.
            let msgOffset := mload(add(0x20, dataStart)) // offset to EVM2AnyMessage
            let msgPtr := add(dataStart, msgOffset) // pointer to message struct

            // IRouterClient.EVM2AnyMessage layout (at msgPtr):
            // +0x00: offset to receiver
            // +0x20: offset to data
            // +0x40: offset to tokenAmounts
            // +0x60: feeToken
            // +0x80: offset to extraArgs
            //
            // Verify feeToken is address(0) - only native token fees are supported
            if mload(add(0x60, msgPtr)) {
                mstore(0x00, 0x6cb99623) // selector for `InvalidFeeToken()`
                revert(0x1c, 0x04)
            }

            // See above comment about malformed offsets.
            let tokensOffset := mload(add(0x40, msgPtr)) // offset to tokenAmounts array
            tokenAmountsPtr := add(msgPtr, tokensOffset) // pointer to tokenAmounts array

            // IRouterClient.EVMTokenAmount[] tokenAmounts array (at tokensPtr, assuming 1 element):
            // +0x00: array length (should be 1)
            // +0x20: tokenAmounts[0].token
            // +0x40: tokenAmounts[0].amount
            //
            // Verify tokenAmounts array has exactly 1 element
            if xor(0x01, mload(tokenAmountsPtr)) {
                mstore(0x00, 0x2c419a85) // selector for `InvalidTokenAmountsLength()`
                revert(0x1c, 0x04)
            }
            // read token from tokenAmounts[0]
            token := mload(add(0x20, tokenAmountsPtr))
        }

        uint256 amount = token.fastBalanceOf(address(this));
        token.safeApproveIfBelow(router, amount);

        assembly ("memory-safe") {
            // Update the amount
            mstore(add(0x40, tokenAmountsPtr), amount)

            // Temporarily clobber the bytes length slot with the function selector
            let len := mload(ccipSendData)
            mstore(ccipSendData, 0x96f4e9f9) // selector for `IRouterClient.ccipSend`

            // Call the `router` with the full balance for fee, any excess is donated to CCIP.
            // `router` is user-provided but we're calling a specific function `IRouterClient.ccipSend`
            // which doesn't clash with restricted targets (AllowanceHolder & Permit2)
            if iszero(call(gas(), router, selfbalance(), add(0x1c, ccipSendData), add(0x04, len), 0x00, 0x00)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }

            // Restore clobbered memory
            mstore(ccipSendData, len)
        }
    }
}

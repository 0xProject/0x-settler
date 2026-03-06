// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";

/// @title CCIP
/// @notice Chainlink CCIP bridge integration for BridgeSettler
/// @dev Handles ERC20 token bridging via CCIP with native token fee payment
contract CCIP {
    using SafeTransferLib for IERC20;

    /// @notice Bridge ERC20 tokens via CCIP, paying fees in native token
    /// @dev The ccipSendData should be pre-encoded ccipSend arguments (without the selector).
    ///      This function will:
    ///      1. Get the full balance of the specified token
    ///      2. Approve the router to spend the tokens
    ///      3. Update the amount in the tokenAmounts[0] of the EVM2AnyMessage
    ///      4. Call ccipSend with the entire native balance as value (for fee payment)
    ///
    ///      Expected ccipSendData layout (ABI encoded):
    ///      - uint64 destinationChainSelector
    ///      - EVM2AnyMessage {
    ///          bytes receiver,
    ///          bytes data,
    ///          EVMTokenAmount[] tokenAmounts, // Must have exactly 1 element
    ///          address feeToken,              // Must be address(0) for native fee
    ///          bytes extraArgs
    ///        }
    ///
    /// @param token The ERC20 token to bridge
    /// @param router The CCIP router address
    /// @param ccipSendData Pre-encoded ccipSend arguments (without selector)
    function bridgeToCCIP(IERC20 token, address router, bytes memory ccipSendData) internal {
        uint256 amount = token.fastBalanceOf(address(this));
        token.safeApproveIfBelow(router, amount);

        // Update the amount in ccipSendData and call the router
        //
        // ccipSendData layout (after bytes length prefix):
        // 0x00: destinationChainSelector (uint64, right-aligned in 32 bytes)
        // 0x20: offset to EVM2AnyMessage (relative to data start)
        //
        // EVM2AnyMessage layout (at msgPtr):
        // +0x00: offset to receiver bytes
        // +0x20: offset to data bytes
        // +0x40: offset to tokenAmounts array
        // +0x60: feeToken address
        // +0x80: offset to extraArgs bytes
        //
        // tokenAmounts array (at tokensPtr, assuming 1 element):
        // +0x00: array length (1)
        // +0x20: tokenAmounts[0].token
        // +0x40: tokenAmounts[0].amount <-- we update this
        assembly ("memory-safe") {
            // Calculate the position of the amount field in tokenAmounts[0]
            let dataStart := add(0x20, ccipSendData) // skip bytes length
            // Malformed offsets are treated as GIGO errors. If they don't result in an OOG/OOM
            // error, they might affect token detection and amount override, which will result in
            // a malformed call to CCIP and most likely a revert.
            let msgOffset := mload(add(0x20, dataStart)) // offset to EVM2AnyMessage
            let msgPtr := add(dataStart, msgOffset) // pointer to message struct

            // Verify feeToken is address(0) - only native token fees are supported
            // feeToken is at msgPtr + 0x60
            if mload(add(0x60, msgPtr)) {
                mstore(0x00, 0x6cb99623) // selector for `InvalidFeeToken()`
                revert(0x1c, 0x04)
            }

            // See above comment about malformed offsets.
            let tokensOffset := mload(add(0x40, msgPtr)) // offset to tokenAmounts array
            let tokensPtr := add(msgPtr, tokensOffset) // pointer to tokenAmounts array

            // Verify tokenAmounts array has exactly 1 element
            if xor(0x01, mload(tokensPtr)) {
                mstore(0x00, 0x2c419a85) // selector for `InvalidTokenAmountsLength()`
                revert(0x1c, 0x04)
            }

            // tokensPtr + 0x00 = array length
            // tokensPtr + 0x20 = tokenAmounts[0].token
            // tokensPtr + 0x40 = tokenAmounts[0].amount
            let amountPtr := add(0x40, tokensPtr)

            // Update the amount
            mstore(amountPtr, amount)

            // Temporarily clobber the bytes length slot with the function selector
            let len := mload(ccipSendData)
            // selector for ccipSend(uint64,(bytes,bytes,(address,uint256)[],address,bytes))
            // keccak256("ccipSend(uint64,(bytes,bytes,(address,uint256)[],address,bytes))") = 0x96f4e9f9...
            mstore(ccipSendData, 0x96f4e9f9)

            // Call the router with the full msg.value (for fee payment)
            // The router is user-provided but we're calling a specific function (ccipSend)
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

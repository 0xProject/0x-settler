// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {SettlerAbstract} from "../SettlerAbstract.sol";

/// @dev Mirrors the relevant subset of Backed's xBridge implementation `BackedCCIPReceiver`
/// (https://etherscan.io/address/0x950570caBf0bBba2B502f1E453D0062CD505E5FE#code).
interface IXBridge {
    function send(
        uint64 destinationChainSelector,
        bytes32 tokenReceiver,
        address token,
        uint256 amount,
        bytes calldata chainSpecificArgs
    ) external payable returns (bytes32 messageId);

    function getDeliveryFeeCost(
        uint64 destinationChainSelector,
        bytes32 tokenReceiver,
        address token,
        uint256 amount,
        bytes calldata chainSpecificArgs
    ) external view returns (uint256);
}

/// @title XBridge
/// @notice BridgeSettler integration for xStocks through Backed's xBridge
abstract contract XBridge is SettlerAbstract {
    using SafeTransferLib for IERC20;

    /// @notice xBridge proxy, the same address on every chain where xBridge is deployed
    /// (https://docs.xstocks.fi/developers/bridge)
    address internal constant XBRIDGE = 0x9eC0e4A4c411493773E01e2ABF4D42395788846b;

    /// @notice Bridge this contract's whole balance of the xStock through xBridge, paying fees in
    /// native token
    /// @param sendData Encoded call to `IXBridge.send` without selector
    function bridgeToXBridge(bytes memory sendData) internal {
        IERC20 token;
        assembly ("memory-safe") {
            // sendData layout in memory:
            // +0x00: bytes length
            // +0x20: destinationChainSelector
            // +0x40: tokenReceiver
            // +0x60: token                     <- read
            // +0x80: amount                    <- override
            // +0xa0: offset to chainSpecificArgs
            // Dirty upper bits in `token` aren't masked; xBridge's ABI decoder rejects them.
            token := mload(add(0x60, sendData))
        }

        uint256 amount = token.fastBalanceOf(address(this));
        token.safeApproveIfBelow(XBRIDGE, amount);

        assembly ("memory-safe") {
            mstore(add(0x80, sendData), amount)

            // Temporarily clobber the bytes length slot with the function selector
            let len := mload(sendData)
            mstore(sendData, 0x5d2a9df2) // selector for `send(uint64,bytes32,address,uint256,bytes)`

            // `XBRIDGE` is hardcoded and doesn't clash with restricted targets (AllowanceHolder & Permit2).
            // Forward the full native balance for the fee; xBridge keeps any excess.
            if iszero(call(gas(), XBRIDGE, selfbalance(), add(0x1c, sendData), add(0x04, len), 0x00, 0x00)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }

            // Restore clobbered length
            mstore(sendData, len)
        }
    }
}

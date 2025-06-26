// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";

interface IBridgeSettlerActions {
    /// @dev Transfer funds from msg.sender Permit2.
    function TRANSFER_FROM(address recipient, ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig)
        external;

    /// @dev Execute swaps in Settler
    function SETTLER_SWAP(address token, uint256 amount, address settler, bytes calldata settlerData) external;

    /// @dev Bridge through a Bridge that follows the approval, transferFrom(msg.sender) interaction
    /// Pre-req: Funded
    function BASIC(address bridgeToken, uint256 bps, address pool, uint256 offset, bytes calldata data) external;

    /// @dev Bridge ERC20 tokens through Relay
    function BRIDGE_ERC20_TO_RELAY(address token, address to, bytes32 requestId) external;

    /// @dev Bridge native tokens through Relay
    function BRIDGE_NATIVE_TO_RELAY(address to, bytes32 requestId) external;

    /// @dev Bridge ERC20 through Mayan
    function BRIDGE_ERC20_TO_MAYAN(address forwarder, address mayanProtocol, bytes calldata protocolData) external;

    /// @dev Bridge native through Mayan
    function BRIDGE_NATIVE_TO_MAYAN(address forwarder, address mayanProtocol, bytes calldata protocolData) external;

    /// @dev Bridge ERC20 through Across
    function BRIDGE_ERC20_TO_ACROSS(address spoke, bytes calldata depositData) external;

    /// @dev Bridge native through Across
    function BRIDGE_NATIVE_TO_ACROSS(address spoke, bytes calldata depositData) external;

    /// @dev Bridge ERC20 through StargateV2
    function BRIDGE_ERC20_TO_STARGATE_V2(address token, address pool, bytes calldata sendData) external;

    /// @dev Bridge native through StargateV2
    function BRIDGE_NATIVE_TO_STARGATE_V2(address pool, uint256 destinationGas, bytes calldata sendData) external;
}
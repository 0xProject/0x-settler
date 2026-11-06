// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";

interface IBridgeSettlerActions {
    /// @dev Transfer funds from msg.sender Permit2.
    function TRANSFER_FROM(address recipient, ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig)
        external;

    /// @dev Execute swaps in Settler
    function SETTLER_SWAP(address token, uint256 amount, address settler, bytes calldata settlerData) external;

    /// @dev Settle an RfqOrder between Maker and BridgeSettler. Transferring funds from the BridgeSettler contract to
    /// maker. Retaining funds in the BridgeSettler contract.
    /// The maker's signature names the taker as counterparty. Filling here rather than in the Settler called by
    /// `SETTLER_SWAP` binds the quote to the user instead of to this shared contract, so nobody else can spend the
    /// signature.
    // Pre-req: Funded
    function RFQ(
        address recipient,
        ISignatureTransfer.PermitTransferFrom memory permit,
        address maker,
        bytes memory makerSig,
        address takerToken,
        uint256 maxTakerAmount
    ) external;

    /// @dev msgValueMin is interpreted as an lower bound on the expected msg.value, not as an exact specification
    function UNDERPAYMENT_CHECK(uint256 msgValueMin) external;

    /// @dev Bridge through a Bridge that follows the approval, transferFrom(msg.sender) interaction
    /// Pre-req: Funded
    function BASIC(address bridgeToken, uint256 ppm, address pool, uint256 offset, bytes calldata data) external;

    /// @dev Bridge ERC20 tokens through Relay
    function BRIDGE_ERC20_TO_RELAY(address token, address to, bytes32 requestId) external;

    /// @dev Bridge native tokens through Relay
    function BRIDGE_NATIVE_TO_RELAY(address to, bytes32 requestId) external;

    /// @dev Bridge ERC20 through Mayan
    function BRIDGE_ERC20_TO_MAYAN(bytes calldata protocolAndData) external;

    /// @dev Bridge native through Mayan
    function BRIDGE_NATIVE_TO_MAYAN(bytes calldata protocolAndData) external;

    /// @dev Bridge ERC20 through Across
    function BRIDGE_ERC20_TO_ACROSS(address spoke, bytes calldata depositData) external;

    /// @dev Bridge native through Across
    function BRIDGE_NATIVE_TO_ACROSS(address spoke, bytes calldata depositData) external;

    /// @dev Bridge through StargateV2
    function BRIDGE_TO_STARGATE_V2(address token, address pool, bytes calldata sendData) external;

    /// @dev Bridge ERC20 through LayerZeroOFT
    function BRIDGE_TO_LAYER_ZERO_OFT(address token, address oft, bytes calldata sendData) external;

    /// @dev Bridge ERC20 through DeBridge
    function BRIDGE_TO_DEBRIDGE(uint256 globalFee, bytes calldata createOrderData) external;

    /// @dev Bridge ERC20 through Chainlink CCIP, paying fees in native token
    function BRIDGE_TO_CCIP(address router, bytes calldata ccipSendData) external;

    /// @dev Bridge WPAXG through Nucleus Teller, paying fees in native token.
    function BRIDGE_TO_NUCLEUS_TELLER(bytes calldata bridgeCallData) external;

    /// @dev Wraps PAXG into WPAXG and bridges the resulting shares through Nucleus Teller,
    /// paying fees in native token.
    function DEPOSIT_AND_BRIDGE_TO_NUCLEUS_TELLER(bytes calldata depositAndBridgeCallData) external;
}

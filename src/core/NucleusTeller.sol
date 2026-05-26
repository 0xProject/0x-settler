// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";

/// @dev Mirrors the relevant subset of paxoslabs/nucleus-boring-vault `AccountantWithRateProviders`.
interface INucleusAccountant {
    function getRateInQuoteSafe(IERC20 quote) external view returns (uint256);
}

/// @dev Mirrors the relevant subset of paxoslabs/nucleus-boring-vault `CrossChainTellerBase`.
/// `BridgeData` follows `src/interfaces/ICrossChainTypes.sol` from that repo.
interface INucleusTeller {
    struct BridgeData {
        uint32 chainSelector;
        address destinationChainReceiver;
        IERC20 bridgeFeeToken;
        uint64 messageGas;
        bytes data;
    }

    function bridge(uint256 shareAmount, BridgeData calldata data) external payable returns (bytes32);

    function depositAndBridge(IERC20 depositAsset, uint256 depositAmount, uint256 minimumMint, BridgeData calldata data)
        external
        payable;

    function previewFee(uint256 shareAmount, BridgeData calldata data) external view returns (uint256);

    function accountant() external view returns (INucleusAccountant);

    function vault() external view returns (IERC20);
}

/// @title NucleusTeller
/// @notice BridgeSettler integration for the Paxos Nucleus WPAXG `CrossChainTellerBase`.
/// @dev Native bridge fees are paid from the contract's full ETH balance. The underlying
/// LayerZero endpoint refunds any excess back to this contract via the Teller's
/// `payable(msg.sender)` refund address.
/// The Teller and WPAXG share token addresses are identical on every chain the deployment
/// supports (Ethereum and Optimism), so they are hardcoded.
contract NucleusTeller {
    using SafeTransferLib for IERC20;

    /// @notice Paxos Nucleus WPAXG `CrossChainTellerBase` (same address on Ethereum and Optimism)
    address internal constant NUCLEUS_TELLER = 0xeE98730AAAdA5e6e092cA69F1AC1B9B554c059dF;

    /// @notice WPAXG share token / Nucleus `BoringVault` (same address on Ethereum and Optimism)
    IERC20 internal constant WPAXG = IERC20(0x5cB5C4d5e8B184A364534bc688DA0553Ccf8F484);

    /// @notice Bridge WPAXG shares held by this contract via the Nucleus Teller.
    /// @param bridgeCallData Encoded args (no selector) to `INucleusTeller.bridge`:
    ///        `(shareAmount, BridgeData)`. `shareAmount` is overridden with this contract's
    ///        WPAXG balance.
    function bridgeToNucleusTeller(bytes memory bridgeCallData) internal {
        uint256 shareAmount = WPAXG.fastBalanceOf(address(this));
        assembly ("memory-safe") {
            // bridgeCallData layout in memory:
            // +0x00: bytes length
            // +0x20: shareAmount               <- OVERRIDE here
            // +0x40: offset to BridgeData tuple
            mstore(add(0x20, bridgeCallData), shareAmount)
        }
        // selector for `bridge(uint256,(uint32,address,address,uint64,bytes))`
        _callTeller(0xa69559d1, bridgeCallData);
    }

    /// @notice Deposit `depositAsset` into the WPAXG BoringVault and bridge the resulting shares.
    /// @param depositAndBridgeCallData Encoded args (no selector) to `INucleusTeller.depositAndBridge`:
    ///        `(depositAsset, depositAmount, minimumMint, BridgeData)`. `depositAmount` is
    ///        overridden with this contract's balance of `depositAsset`.
    function depositAndBridgeToNucleusTeller(bytes memory depositAndBridgeCallData) internal {
        IERC20 depositAsset;
        assembly ("memory-safe") {
            // depositAndBridgeCallData layout in memory:
            // +0x00: bytes length
            // +0x20: depositAsset              <- read
            // +0x40: depositAmount             <- OVERRIDE below
            // +0x60: minimumMint
            // +0x80: offset to BridgeData tuple
            depositAsset := mload(add(0x20, depositAndBridgeCallData))
        }

        uint256 depositAmount = depositAsset.fastBalanceOf(address(this));
        depositAsset.safeApproveIfBelow(address(WPAXG), depositAmount);

        assembly ("memory-safe") {
            mstore(add(0x40, depositAndBridgeCallData), depositAmount)
        }
        // selector for `depositAndBridge(address,uint256,uint256,(uint32,address,address,uint64,bytes))`
        _callTeller(0xbfe1a0f2, depositAndBridgeCallData);
    }

    /// @dev Calls `NUCLEUS_TELLER` with `selector` prepended to `data`, forwarding the full ETH balance.
    function _callTeller(uint256 selector, bytes memory data) private {
        assembly ("memory-safe") {
            let len := mload(data)
            // Temporarily clobber the bytes length slot with the function selector
            mstore(data, selector)

            // `NUCLEUS_TELLER` is hardcoded and doesn't clash with restricted targets (AllowanceHolder & Permit2).
            // `selfbalance()` is safe: the underlying LayerZero endpoint refunds any excess to this
            // contract via the Teller's `payable(msg.sender)` refund address.
            if iszero(call(gas(), NUCLEUS_TELLER, selfbalance(), add(0x1c, data), add(0x04, len), 0x00, 0x00)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            // Restore clobbered length
            mstore(data, len)
        }
    }
}

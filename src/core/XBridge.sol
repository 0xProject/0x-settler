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

    /// @notice Bridge this contract's whole balance of the xStock through xBridge, paying the CCIP
    /// fee in native token.
    /// @param recipient Receiver on the destination chain, an EVM address left-padded to 32 bytes or
    /// a Solana account
    /// @param chainSpecificArgs Ignored for EVM destinations. Solana destinations need the accounts
    /// that CCIP passes to the receiving program.
    function bridgeToXBridge(
        bytes32 recipient,
        IERC20 token,
        uint64 destinationChainSelector,
        bytes memory chainSpecificArgs
    ) internal {
        uint256 amount = token.fastBalanceOf(address(this));
        token.safeApproveIfBelow(XBRIDGE, amount);

        bytes memory args = abi.encode(destinationChainSelector, recipient, token, amount, chainSpecificArgs);
        assembly ("memory-safe") {
            // Both calls take the same arguments. Encoding them once and writing each selector over
            // the length slot is smaller and cheaper than two Solidity calls. Nothing reads the
            // encoding afterwards, so the length isn't restored.
            let len := mload(args)
            mstore(args, 0x387cb1d9) // selector for `getDeliveryFeeCost(uint64,bytes32,address,uint256,bytes)`
            if iszero(staticcall(gas(), XBRIDGE, add(0x1c, args), add(0x04, len), 0x00, 0x20)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            if gt(0x20, returndatasize()) { revert(0x00, 0x00) }

            // xBridge keeps any native sent above the fee, and only Backed can withdraw it. Pay the
            // exact fee so that the rest stays here for a later action to return to the taker.
            mstore(args, 0x5d2a9df2) // selector for `send(uint64,bytes32,address,uint256,bytes)`
            if iszero(call(gas(), XBRIDGE, mload(0x00), add(0x1c, args), add(0x04, len), 0x00, 0x00)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
        }
    }
}

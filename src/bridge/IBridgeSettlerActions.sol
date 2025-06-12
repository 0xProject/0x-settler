// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";

interface IBridgeSettlerActions {
    /// @dev Transfer funds from msg.sender Permit2.
    function TRANSFER_FROM(address recipient, ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig)
        external;

    /// @dev Execute swaps in Settler
    function SETTLER_SWAP(address token, uint256 amount, address settler, bytes calldata settlerData) external;

    /// @dev Bridge through a generic bridge
    /// @dev Entire balance of token is bridged
    function BRIDGE(address token, address bridge, bytes calldata bridgeData) external;
}
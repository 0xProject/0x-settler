// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {ISettlerBase} from "../interfaces/ISettlerBase.sol";

interface IBridgeSettlerActions {
    /// @dev Execute swaps in Settler
    function SETTLER_SWAP(address token, uint256 amount, address settler, bytes calldata settlerData) external;

    /// @dev Bridge through a generic bridge
    /// @dev Entire balance of token is bridged
    function BRIDGE(address token, address bridge, bytes calldata bridgeData) external;

    /// @dev Move assets from the AllowanceHolder to the BridgeSettler
    function TAKE(address token, uint256 amount) external;
}
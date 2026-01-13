// SPDX-License-Identifier: AGPL-3.0-or-later
pragma solidity ^0.8.19;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

interface INativeMetaTransaction {
    function executeMetaTransaction(
        address userAddress,
        bytes memory functionSignature,
        bytes32 sigR,
        bytes32 sigS,
        uint8 sigV
    ) external payable returns (bytes memory);
    function getNonce(address userAddress) external view returns (uint256);
    function getDomainSeparator() external view returns (bytes32);
}

interface IERC20MetaTransaction is INativeMetaTransaction, IERC20 {}

// SPDX-License-Identifier: AGPL-3.0-or-later
pragma solidity ^0.8.19;

import {IERC20PermitCommon} from "./IERC2612.sol";

interface INativeMetaTransaction {
    function executeMetaTransaction(
        address userAddress,
        bytes memory functionSignature,
        bytes32 sigR,
        bytes32 sigS,
        uint8 sigV
    ) external payable returns (bytes memory);
}

interface IERC20MetaTransaction is IERC20PermitCommon, INativeMetaTransaction {}

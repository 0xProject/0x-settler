// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {ISettlerBase} from "./ISettlerBase.sol";

interface ISettlerMetaTxn is ISettlerBase {
    function executeMetaTxn(
        AllowedSlippage calldata slippage,
        bytes[] calldata actions,
        bytes32 /* zid & affiliate */,
        address msgSender,
        bytes calldata sig
    ) external returns (bool);
 
    event MetaTxnExecuted(
        address indexed signer,
        address indexed relayer,
        uint256 actionsLength,
        bytes32 actionsHash
    );
}

}

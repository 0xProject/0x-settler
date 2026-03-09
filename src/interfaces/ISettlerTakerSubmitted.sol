// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {ISettlerBase} from "./ISettlerBase.sol";

interface ISettlerTakerSubmitted is ISettlerBase {
    function execute(
        AllowedSlippage calldata slippage,
        bytes[] calldata actions,
        bytes32 /* zid & affiliate */
    )
        external
        payable
        returns (bool);

    function executeWithPermit(
        AllowedSlippage calldata slippage,
        bytes[] calldata actions,
        bytes32 /* zid & affiliate */,
        bytes memory permitData
    ) external payable returns (bool);
}

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IRevertTarget} from "./MockRevertTarget.sol";

interface IExecReturnHarness {
    function execReturnHarness(
        address operator,
        address token,
        uint256 amount,
        address payable target,
        bytes calldata data
    ) external payable returns (bytes memory);
}

// Provides the memory->calldata boundary needed to invoke exec with a FIXED
// `data` equal to MockRevertTarget.triggerRevert()'s selector.

contract MockExecRevertCaller {
    IExecReturnHarness allowanceHolder; // linked to AllowanceHolderExecReturnHarness (internal: no getter)

    function callExecToRevertTarget(
        address operator,
        address token,
        uint256 amount,
        address payable target
    ) external payable returns (bytes memory) {
        bytes memory data = abi.encodeWithSelector(IRevertTarget.triggerRevert.selector);
        return allowanceHolder.execReturnHarness{value: msg.value}(operator, token, amount, target, data);
    }
}

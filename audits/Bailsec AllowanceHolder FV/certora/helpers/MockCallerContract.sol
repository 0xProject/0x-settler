// SPDX-License-Identifier: MIT
pragma solidity =0.8.25;

import {IAllowanceHolderExtended} from "certora/helpers/IAllowanceHolderExtended.sol";

contract MockCallerContract {

    //state variable to link to the AllowanceHolderHarness
    IAllowanceHolderExtended public target;

    constructor(IAllowanceHolderExtended _target) {
        target = _target;
    }

    function callTransferFrom(
        address token,
        address owner, 
        address recipient, 
        uint256 amount
    ) external {
        target.transferFrom(token, owner, recipient, amount);
    }

    function callExec(
        address operator,
        address token, 
        uint256 amount,
        address payable targetAddress, 
        bytes calldata data
    ) external {
        target.exec(operator, token, amount, targetAddress, data);
    }

    function callBalanceOf(address owner) external view returns (bool success, uint256 retSize) {
        (success, ) = address(target).staticcall(
            abi.encodeWithSelector(IAllowanceHolderExtended.balanceOf.selector, owner)
        );
        assembly ("memory-safe") {
            retSize := returndatasize()
        }
    }

    function callWithSelector(uint32 sel, bytes calldata rest) external returns (bool success) {
        (success, ) = address(target).call(bytes.concat(bytes4(sel), rest));
    }

    function callTransferFromRawWithValue(
        uint256 rawToken,
        uint256 rawOwner,
        uint256 rawRecipient,
        uint256 amount
    ) external payable returns (bool success) {
        bytes4 sel = IAllowanceHolderExtended.transferFrom.selector;
        (success, ) = address(target).call{value: msg.value}(
            abi.encodePacked(sel, rawToken, rawOwner, rawRecipient, amount)
        );
    }

    function callExecRaw(
        uint256 rawOperator,
        uint256 rawToken,
        uint256 amount,
        uint256 rawTarget,
        bytes calldata data
    ) external returns (bool success) {
        bytes4 sel = IAllowanceHolderExtended.exec.selector;
        bytes memory payload = abi.encodePacked(
            sel, rawOperator, rawToken, amount, rawTarget,
            uint256(0xa0), uint256(data.length), data
        );
        (success, ) = address(target).call(payload);
    }

    function callExecEndToEnd(
        address operator,
        address token,
        uint256 amount,
        address execTarget,
        bytes calldata data
    ) external {
        bytes memory extendedData = bytes.concat(bytes4(keccak256("endToEndTest()")), data);
        target.exec(operator, token, amount, payable(execTarget), extendedData);
    }
}
// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.25;

import {AllowanceHolder} from "src/allowanceholder/AllowanceHolder.sol";
import {IAllowanceHolder} from "src/allowanceholder/IAllowanceHolder.sol";
import {IERC20} from "@forge-std/interfaces/IERC20.sol";

contract AllowanceHolderHarness is AllowanceHolder {

    uint256 public immutable deployChainId;

    constructor() {
        deployChainId = block.chainid;
    }

    function execHarness(
        address operator, 
        address token, 
        uint256 amount, 
        address payable target, 
        bytes calldata data
    ) external payable returns (bytes memory result) {
        exec(operator, token, amount, target, data);
    }

    function transferFromHarness(
        address token,
        address owner,
        address recipient,
        uint256 amount
    ) external{
        transferFrom(token, owner, recipient, amount);
    }

    function rejectIfERC20Harness(
        address payable maybeERC20,
        bytes calldata data
    ) external view returns (address target) {
        target = _rejectIfERC20Inner(maybeERC20, data);
    }

    //overwrite the function to bypass the DANGEROUS_freeMemory modifier
    function _rejectIfERC20(address payable maybeERC20, bytes calldata data) internal override view  {
        _rejectIfERC20Inner(maybeERC20, data);

    }

    // added data to simulate an internal call to the _msgSender function
    function _msgSenderHarness(bytes calldata data) external view returns (address) {
        return _msgSender();
    }

    function selTransferFromHarness() external pure returns (bytes4) { 
        return IAllowanceHolder.transferFrom.selector; 
    }
    
    function selExecHarness() external pure returns (bytes4) {
        return IAllowanceHolder.exec.selector; 
    }
    
    function selBalanceOfHarness() external pure returns (bytes4) {
        return IERC20.balanceOf.selector;
    }

    function computeRejectTarget(bytes calldata data) external pure returns (address target) {
        if (data.length > 0x10) {
            target = address(uint160(bytes20(data[0x10:])));
        }
        if (target <= address(0xffff)) {
            target = address(0xdead);
        }
    }

    // Single-frame check: both reads observe the SAME msg.data of THIS call,
    // so _msgSender() (self-call branch) must equal the tail of this frame's
    // calldata. The `data` argument only exists to give msg.data a >=20-byte tail.
    function msgSenderVsTailHarness(bytes calldata data)
        external
        view
        returns (address fromMsgSender, address fromTail)
    {
        fromMsgSender = _msgSender();
        fromTail = address(bytes20(msg.data[msg.data.length - 20:]));
    }

    // Returns exec's raw returned bytes.
    function execReturnHarness(
        address operator,
        address token,
        uint256 amount,
        address payable target,
        bytes calldata data
    ) external payable returns (bytes memory result) {
        result = exec(operator, token, amount, target, data);
    }

    // Surfaces BOTH the byte-length and the first 32-byte word of exec's returndata
    function execReturnWordAndLengthHarness(
        address operator,
        address token,
        uint256 amount,
        address payable target,
        bytes calldata data
    ) external payable returns (uint256 word, uint256 len) {
        bytes memory result = exec(operator, token, amount, target, data);
        len = result.length;
        word = abi.decode(result, (uint256));
    }
}

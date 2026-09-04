// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IAllowanceHolder} from "src/allowanceholder/IAllowanceHolder.sol";

contract MockActiveCallbackTarget {

    uint256 public amount;
    address public token;
    address public owner;
    address public recipient;
    address public allowanceHolder;

    fallback() external payable {
        //call msg.sender.transferFrom()
        (bool success, ) = allowanceHolder.call(abi.encodeWithSelector(IAllowanceHolder.transferFrom.selector, token, owner, recipient, amount));
        require(success, "Transfer failed");
    }

}
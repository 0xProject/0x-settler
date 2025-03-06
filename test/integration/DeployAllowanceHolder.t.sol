// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IAllowanceHolder} from "src/allowanceholder/IAllowanceHolder.sol";

import {Vm} from "@forge-std/Vm.sol";

contract DeployAllowanceHolder {
    Vm private constant vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    IAllowanceHolder internal allowanceHolder;

    function _deployAllowanceHolder() internal returns (IAllowanceHolder) {
        allowanceHolder = IAllowanceHolder(0x0000000000001fF3684f28c67538d4D072C22734);
        vm.etch(address(allowanceHolder), vm.getDeployedCode("AllowanceHolder.sol:AllowanceHolder"));
        vm.label(address(allowanceHolder), "AllowanceHolder");
        return allowanceHolder;
    }
}

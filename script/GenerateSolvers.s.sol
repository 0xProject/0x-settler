// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Script} from "@forge-std/Script.sol";

contract GenerateSolvers is Script {
    function run(uint32 count) external view returns (address[] memory solvers) {
        string memory mnemonic = vm.envString("SOLVER_MNEMONIC");
        solvers = new address[](count);
        for (uint32 i; i < count; ++i) {
            solvers[i] = vm.addr(vm.deriveKey(mnemonic, i));
        }
    }
}

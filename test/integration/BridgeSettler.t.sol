// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {BridgeSettlerTestBase} from "../unit/BridgeSettler.t.sol";
import {MainnetSettler as Settler} from "src/chains/Mainnet/TakerSubmitted.sol";
import {MainnetDefaultFork} from "./BaseForkTest.t.sol";
import {IDeployer} from "src/deployer/IDeployer.sol";
import {DEPLOYER} from "src/deployer/DeployerAddress.sol";
import {ISettlerTakerSubmitted} from "src/interfaces/ISettlerTakerSubmitted.sol";

abstract contract BridgeSettlerIntegrationTest is BridgeSettlerTestBase, MainnetDefaultFork {
    function testBlockNumber() internal pure virtual override returns (uint256) {
        return 22719835;
    }
    
    function setUp() public virtual override {
        // deploy BridgeSettler
        super.setUp();
        vm.createSelectFork(testChainId(), testBlockNumber());
        settler = ISettlerTakerSubmitted(IDeployer(DEPLOYER).ownerOf(2));
        vm.label(address(settler), "Settler");
    }
}
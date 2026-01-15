// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {AllowanceHolder} from "src/allowanceholder/AllowanceHolderOld.sol";
import {ALLOWANCE_HOLDER} from "src/allowanceholder/IAllowanceHolder.sol";

import {BridgeSettlerTestBase} from "../unit/BridgeSettler.t.sol";
import {MainnetDefaultFork} from "./BaseForkTest.t.sol";
import {IDeployer} from "src/deployer/IDeployer.sol";
import {DEPLOYER} from "src/deployer/DeployerAddress.sol";
import {ISettlerTakerSubmitted} from "src/interfaces/ISettlerTakerSubmitted.sol";
import {MainnetBridgeSettler} from "src/chains/Mainnet/BridgeSettler.sol";


abstract contract BridgeSettlerIntegrationTest is BridgeSettlerTestBase, MainnetDefaultFork {
    function _testBlockNumber() internal pure virtual override returns (uint256) {
        return 22719835;
    }

    function _testBridgeSettler() internal virtual override {
        bridgeSettler = new MainnetBridgeSettler(bytes20(0));
    }

    function setUp() public virtual override {
        vm.etch(address(ALLOWANCE_HOLDER), address(new AllowanceHolder()).code);
        vm.makePersistent(address(ALLOWANCE_HOLDER));

        // deploy BridgeSettler
        super.setUp();
        vm.createSelectFork(_testChainId(), _testBlockNumber());
        vm.setEvmVersion("cancun");
        settler = ISettlerTakerSubmitted(IDeployer(DEPLOYER).ownerOf(2));
        vm.label(address(settler), "Settler");
    }
}

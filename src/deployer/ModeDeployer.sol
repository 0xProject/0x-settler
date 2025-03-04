// SPDX-License-Identifier: MIT
pragma solidity =0.8.25;

import {Deployer} from "./Deployer.sol";
import {DEPLOYER} from "./DeployerAddress.sol";
import {MODE_SFS} from "../chains/Mode/IModeSFS.sol";

/// @custom:security-contact security@0x.org
contract ModeDeployer is Deployer {
    uint256 public immutable sfsTokenId;

    constructor(uint256 version) Deployer(version) {
        assert(block.chainid == 34443);
        if (DEPLOYER.code.length == 0) {
            assert(_implVersion == 1);
            sfsTokenId = MODE_SFS.register(0xf36b9f50E59870A24F42F9Ba43b2aD0A4b8f2F51);
        } else {
            MODE_SFS.assign(sfsTokenId = MODE_SFS.getTokenId(DEPLOYER));
        }
    }

    function initialize(address initialOwner) public override {
        assert(block.chainid == 34443);
        if (_implVersion == 1) {
            MODE_SFS.assign(sfsTokenId);
        }
        super.initialize(initialOwner);
    }
}

// SPDX-License-Identifier: MIT
pragma solidity =0.8.25;

import {Deployer} from "./Deployer.sol";
import {BLAST, BlastYieldMode, BlastGasMode} from "../chains/IBlast.sol";

/// @custom:security-contact security@0x.org
contract BlastDeployer is Deployer {
    constructor(uint256 version) Deployer(version) {
        assert(block.chainid == 81457);
        BLAST.configure(
            BlastYieldMode.AUTOMATIC,
            BlastGasMode.CLAIMABLE,
            BlastDeployer(0x00000000000004533Fe15556B1E086BB1A72cEae).owner()
        );
    }

    function initialize(address initialOwner) public override {
        assert(block.chainid == 81457);
        BLAST.configure(BlastYieldMode.AUTOMATIC, BlastGasMode.CLAIMABLE, owner());
        super.initialize(initialOwner);
    }
}

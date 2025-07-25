// SPDX-License-Identifier: MIT
pragma solidity =0.8.25;

import {BridgeSettler, BridgeSettlerBase} from "../../bridge/BridgeSettler.sol";

contract AvalancheBridgeSettler is BridgeSettler {
    constructor(bytes20 gitCommit) BridgeSettlerBase(gitCommit) {
        assert(block.chainid == 43114 || block.chainid == 31337);
    }
}

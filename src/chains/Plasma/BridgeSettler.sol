// SPDX-License-Identifier: MIT
pragma solidity =0.8.25;

import {SettlerAbstract} from "../../SettlerAbstract.sol";
import {IBridgeSettlerActions} from "../../bridge/IBridgeSettlerActions.sol";
import {BridgeSettler, BridgeSettlerBase} from "../../bridge/BridgeSettler.sol";

contract PlasmaBridgeSettler is BridgeSettler {
    constructor(bytes20 gitCommit) BridgeSettlerBase(gitCommit) {
        assert(block.chainid == 9745 || block.chainid == 31337);
    }

    function _dispatch(uint256 i, uint256 action, bytes calldata data)
        internal
        override(BridgeSettlerBase, SettlerAbstract)
        returns (bool)
    {
        if (super._dispatch(i, action, data)) {
            return true;
        } else {
            return false;
        }
        return true;
    }
}

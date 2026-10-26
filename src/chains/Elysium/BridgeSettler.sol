// SPDX-License-Identifier: MIT
pragma solidity =0.8.34;

import {IBridgeSettlerActions} from "../../bridge/IBridgeSettlerActions.sol";
import {Permit2PaymentAbstract} from "../../core/Permit2PaymentAbstract.sol";
import {BridgeSettler, BridgeSettlerBase} from "../../bridge/BridgeSettler.sol";

contract ElysiumBridgeSettler is BridgeSettler {
    constructor(bytes20 gitCommit) BridgeSettlerBase(gitCommit) {
        assert(block.chainid == 99901 || block.chainid == 31337);
    }

    function _dispatch(uint256 i, uint256 action, bytes calldata data)
        internal
        override(BridgeSettlerBase)
        returns (bool)
    {
        if (super._dispatch(i, action, data)) {
            return true;
        } else {
            return false;
        }
        return true;
    }

    function _isRestrictedTarget(address target)
        internal
        view
        override(BridgeSettler /*, Permit2PaymentAbstract */)
        returns (bool)
    {
        return super._isRestrictedTarget(target);
    }
}

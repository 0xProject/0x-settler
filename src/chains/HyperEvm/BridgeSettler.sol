// SPDX-License-Identifier: MIT
pragma solidity =0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SettlerAbstract} from "../../SettlerAbstract.sol";
import {IBridgeSettlerActions} from "../../bridge/IBridgeSettlerActions.sol";
import {BridgeSettler, BridgeSettlerBase} from "../../bridge/BridgeSettler.sol";
import {DeBridge} from "../../core/DeBridge.sol";

contract HyperEvmBridgeSettler is BridgeSettler, DeBridge {
    constructor(bytes20 gitCommit) BridgeSettlerBase(gitCommit) {
        assert(block.chainid == 999 || block.chainid == 31337);
    }

    function _dispatch(uint256 i, uint256 action, bytes calldata data)
        internal
        override(BridgeSettlerBase, SettlerAbstract)
        returns (bool)
    {
        if (super._dispatch(i, action, data)) {
            return true;
        } else if (action == uint32(IBridgeSettlerActions.BRIDGE_TO_DEBRIDGE.selector)) {
            (uint256 globalFee, bytes memory createOrderData) = abi.decode(data, (uint256, bytes));
            bridgeToDeBridge(globalFee, createOrderData);
        } else {
            return false;
        }
    }
}

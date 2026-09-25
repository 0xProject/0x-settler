// SPDX-License-Identifier: MIT
pragma solidity =0.8.34;

import {IBridgeSettlerActions} from "../../bridge/IBridgeSettlerActions.sol";
import {BridgeSettler, BridgeSettlerBase} from "../../bridge/BridgeSettler.sol";

import {BlockTip403Registry} from "./BlockTip403Registry.sol";

import {Across} from "../../core/Across.sol";

contract TempoBridgeSettler is BridgeSettler, BlockTip403Registry, Across {
    constructor(bytes20 gitCommit) BridgeSettlerBase(gitCommit) {
        assert(block.chainid == 4217 || block.chainid == 31337);
    }

    function _dispatch(uint256 i, uint256 action, bytes calldata data)
        internal
        override(BridgeSettlerBase)
        returns (bool)
    {
        if (super._dispatch(i, action, data)) {
            return true;
        } else if (action == uint32(IBridgeSettlerActions.BRIDGE_ERC20_TO_ACROSS.selector)) {
            (address spoke, bytes memory depositData) = abi.decode(data, (address, bytes));
            bridgeERC20ToAcross(spoke, depositData);
        } else if (action == uint32(IBridgeSettlerActions.BRIDGE_NATIVE_TO_ACROSS.selector)) {
            (address spoke, bytes memory depositData) = abi.decode(data, (address, bytes));
            bridgeNativeToAcross(spoke, depositData);
        } else {
            return false;
        }
        return true;
    }

    // I hate Solidity inheritance
    function _isRestrictedTarget(address target)
        internal
        view
        virtual
        override(BridgeSettler, BlockTip403Registry)
        returns (bool)
    {
        return super._isRestrictedTarget(target);
    }
}

// SPDX-License-Identifier: MIT
pragma solidity =0.8.25;

import {SettlerAbstract} from "../../SettlerAbstract.sol";
import {IBridgeSettlerActions} from "../../bridge/IBridgeSettlerActions.sol";
import {BridgeSettler, BridgeSettlerBase} from "../../bridge/BridgeSettler.sol";
import {Mayan} from "../../core/Mayan.sol";

contract AvalancheBridgeSettler is BridgeSettler, Mayan {
    constructor(bytes20 gitCommit) BridgeSettlerBase(gitCommit) {
        assert(block.chainid == 43114 || block.chainid == 31337);
    }

    function _dispatch(uint256 i, uint256 action, bytes calldata data)
        internal
        override(BridgeSettlerBase, SettlerAbstract)
        returns (bool)
    {
        if (super._dispatch(i, action, data)) {
            return true;
        } else if (action == uint32(IBridgeSettlerActions.BRIDGE_ERC20_TO_MAYAN.selector)) {
            (address forwarder, bytes memory protocolAndData) = abi.decode(data, (address, bytes));
            bridgeERC20ToMayan(forwarder, protocolAndData);
        } else if (action == uint32(IBridgeSettlerActions.BRIDGE_NATIVE_TO_MAYAN.selector)) {
            (address forwarder, bytes memory protocolAndData) = abi.decode(data, (address, bytes));
            bridgeNativeToMayan(forwarder, protocolAndData);
        } else {
            return false;
        }
        return true;
    }
}

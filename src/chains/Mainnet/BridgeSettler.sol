// SPDX-License-Identifier: MIT
pragma solidity =0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SettlerAbstract} from "../../SettlerAbstract.sol";
import {IBridgeSettlerActions} from "../../bridge/IBridgeSettlerActions.sol";
import {BridgeSettler, BridgeSettlerBase} from "../../bridge/BridgeSettler.sol";
import {Across} from "../../core/Across.sol";
import {Mayan} from "../../core/Mayan.sol";
import {StargateV2} from "../../core/StargateV2.sol";

contract MainnetBridgeSettler is BridgeSettler, Across, Mayan, StargateV2 {
    constructor(bytes20 gitCommit) BridgeSettlerBase(gitCommit) {
        assert(block.chainid == 1 || block.chainid == 31337);
    }

    function _dispatch(uint256 i, uint256 action, bytes calldata data)
        internal
        override(BridgeSettlerBase, SettlerAbstract)
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
        } else if (action == uint32(IBridgeSettlerActions.BRIDGE_ERC20_TO_MAYAN.selector)) {
            (address forwarder, bytes memory protocolAndData) = abi.decode(data, (address, bytes));
            bridgeERC20ToMayan(forwarder, protocolAndData);
        } else if (action == uint32(IBridgeSettlerActions.BRIDGE_NATIVE_TO_MAYAN.selector)) {
            (address forwarder, bytes memory protocolAndData) = abi.decode(data, (address, bytes));
            bridgeNativeToMayan(forwarder, protocolAndData);
        } else if (action == uint32(IBridgeSettlerActions.BRIDGE_ERC20_TO_STARGATE_V2.selector)) {
            (IERC20 token, address pool, bytes memory sendData) = abi.decode(data, (IERC20, address, bytes));
            bridgeERC20ToStargateV2(token, pool, sendData);
        } else if (action == uint32(IBridgeSettlerActions.BRIDGE_NATIVE_TO_STARGATE_V2.selector)) {
            (address pool, uint256 destinationGas, bytes memory sendData) = abi.decode(data, (address, uint256, bytes));
            bridgeNativeToStargateV2(pool, destinationGas, sendData);
        } else {
            return false;
        }
        return true;
    }
}

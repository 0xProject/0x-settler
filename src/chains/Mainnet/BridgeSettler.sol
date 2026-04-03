// SPDX-License-Identifier: MIT
pragma solidity =0.8.33;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SettlerAbstract} from "../../SettlerAbstract.sol";
import {IBridgeSettlerActions} from "../../bridge/IBridgeSettlerActions.sol";
import {BridgeSettler, BridgeSettlerBase} from "../../bridge/BridgeSettler.sol";
import {Across} from "../../core/Across.sol";
import {Mayan} from "../../core/Mayan.sol";
import {StargateV2} from "../../core/StargateV2.sol";
import {DeBridge} from "../../core/DeBridge.sol";

contract MainnetBridgeSettler is BridgeSettler, Across, Mayan, StargateV2, DeBridge {
    constructor(bytes20 gitCommit) BridgeSettlerBase(gitCommit) {
        assert(block.chainid == 1 || block.chainid == 31337);
    }

    function _dispatch(uint256 i, uint256 action, bytes calldata data) internal override returns (bool) {
        if (super._dispatch(i, action, data)) {
            return true;
        } else if (action == uint32(IBridgeSettlerActions.BRIDGE_ERC20_TO_ACROSS.selector)) {
            (address spoke, bytes memory depositData) = abi.decode(data, (address, bytes));
            bridgeERC20ToAcross(spoke, depositData);
        } else if (action == uint32(IBridgeSettlerActions.BRIDGE_NATIVE_TO_ACROSS.selector)) {
            (address spoke, bytes memory depositData) = abi.decode(data, (address, bytes));
            bridgeNativeToAcross(spoke, depositData);
        } else if (action == uint32(IBridgeSettlerActions.BRIDGE_ERC20_TO_MAYAN.selector)) {
            bytes memory protocolAndData = abi.decode(data, (bytes));
            bridgeERC20ToMayan(protocolAndData);
        } else if (action == uint32(IBridgeSettlerActions.BRIDGE_NATIVE_TO_MAYAN.selector)) {
            bytes memory protocolAndData = abi.decode(data, (bytes));
            bridgeNativeToMayan(protocolAndData);
        } else if (action == uint32(IBridgeSettlerActions.BRIDGE_TO_STARGATE_V2.selector)) {
            (IERC20 token, address pool, bytes memory sendData) = abi.decode(data, (IERC20, address, bytes));
            bridgeToStargateV2(token, pool, sendData);
        } else if (action == uint32(IBridgeSettlerActions.BRIDGE_TO_DEBRIDGE.selector)) {
            (uint256 globalFee, bytes memory createOrderData) = abi.decode(data, (uint256, bytes));
            bridgeToDeBridge(globalFee, createOrderData);
        } else {
            return false;
        }
        return true;
    }
}

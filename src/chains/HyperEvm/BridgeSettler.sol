// SPDX-License-Identifier: MIT
pragma solidity =0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SettlerAbstract} from "../../SettlerAbstract.sol";
import {IBridgeSettlerActions} from "../../bridge/IBridgeSettlerActions.sol";
import {BridgeSettler, BridgeSettlerBase} from "../../bridge/BridgeSettler.sol";
import {LayerZeroOFT} from "../../core/LayerZeroOFT.sol";

contract HyperEvmBridgeSettler is BridgeSettler, LayerZeroOFT {
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
        } else if (action == uint32(IBridgeSettlerActions.BRIDGE_ERC20_TO_LAYER_ZERO_OFT.selector)) {
            (IERC20 token, address oft, bytes memory sendData) = abi.decode(data, (IERC20, address, bytes));
            bridgeLayerZeroOFT(token, oft, sendData);
        } else {
            return false;
        }
    }
}

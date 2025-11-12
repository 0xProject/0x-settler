// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {IERC721Owner} from "../IERC721Owner.sol";
import {DEPLOYER} from "../deployer/DeployerAddress.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {IBridgeSettlerActions} from "./IBridgeSettlerActions.sol";
import {ALLOWANCE_HOLDER} from "../allowanceholder/IAllowanceHolder.sol";
import {Revert} from "../utils/Revert.sol";
import {uint512} from "../utils/512Math.sol";
import {IDeployer} from "../deployer/IDeployer.sol";
import {FastDeployer} from "../deployer/FastDeployer.sol";
import {Basic} from "../core/Basic.sol";
import {Relay} from "../core/Relay.sol";
import {LayerZeroOFT} from "../core/LayerZeroOFT.sol";
import {Underpayment} from "../core/SettlerErrors.sol";

abstract contract BridgeSettlerBase is Basic, Relay, LayerZeroOFT {
    using SafeTransferLib for IERC20;
    using Revert for bool;
    using FastDeployer for IDeployer;

    event GitCommit(bytes20 indexed);

    error CounterfeitSettler(address counterfeitSettler);

    IDeployer internal constant _DEPLOYER = IDeployer(DEPLOYER);
    uint128 internal constant _SETTLER_TAKER_SUBMITTED_TOKENID = 2;

    constructor(bytes20 gitCommit) {
        if (block.chainid != 31337) {
            emit GitCommit(gitCommit);
            assert(IERC721Owner(DEPLOYER).ownerOf(_tokenId()) == address(this));
        } else {
            assert(gitCommit == bytes20(0));
        }
    }

    function _requireValidSettler(address settler) private view {
        // Any revert in `ownerOf` or `prev` will be bubbled. Any error in ABIDecoding the result
        // will result in a revert without a reason string.
        if (
            _DEPLOYER.fastOwnerOf(_SETTLER_TAKER_SUBMITTED_TOKENID) != settler
                && _DEPLOYER.fastPrev(_SETTLER_TAKER_SUBMITTED_TOKENID) != settler
        ) {
            assembly ("memory-safe") {
                mstore(0x14, settler)
                mstore(0x00, 0x7a1cd8fa000000000000000000000000) // selector for `CounterfeitSettler(address)` with `settler`'s padding
                revert(0x10, 0x24)
            }
        }
    }

    function _dispatch(uint256, uint256 action, bytes calldata data) internal virtual override returns (bool) {
        if (action == uint32(IBridgeSettlerActions.SETTLER_SWAP.selector)) {
            (address token, uint256 amount, address settler, bytes memory settlerData) =
                abi.decode(data, (address, uint256, address, bytes));
            // Swaps are going to be directed to Settler, so `settler` must be an active settler
            _requireValidSettler(settler);
            if (token == address(ETH_ADDRESS)) {
                // Native token swap
                // Settler address was validated to be a correct settler, so we pass the
                // arbitrary data as we know it is not a restricted target.
                // Eth sent to Settler is available to any action being executed making this
                // call subsectible to MEV attacks that force the swap to its Slippage limit.
                (bool success, bytes memory retData) = settler.call{value: amount}(settlerData);
                success.maybeRevert(retData);
            } else {
                // To effectively do a swap we need to make funds accessible to Settler
                // It is not possible to call it directly as the taker is going to be the BridgeSettler
                // instead of the user, so, user assets needs to be pulled to BridgeSettler before
                // attempting to do this swap.
                // Settler can take over the assets if settlerData starts with a VIP action making this
                // call subsectible to MEV attacks that force the swap to its Slippage limit.
                IERC20(token).safeApproveIfBelow(address(ALLOWANCE_HOLDER), amount);
                ALLOWANCE_HOLDER.exec(settler, token, amount, payable(settler), settlerData);
            }
        } else if (action == uint32(IBridgeSettlerActions.BASIC.selector)) {
            (address bridgeToken, uint256 bps, address pool, uint256 offset, bytes memory bridgeData) =
                abi.decode(data, (address, uint256, address, uint256, bytes));

            basicSellToPool(IERC20(bridgeToken), bps, pool, offset, bridgeData);
        } else if (action == uint32(IBridgeSettlerActions.BRIDGE_ERC20_TO_RELAY.selector)) {
            (address token, address to, bytes32 requestId) = abi.decode(data, (address, address, bytes32));
            bridgeERC20ToRelay(IERC20(token), to, requestId);
        } else if (action == uint32(IBridgeSettlerActions.BRIDGE_NATIVE_TO_RELAY.selector)) {
            (address to, bytes32 requestId) = abi.decode(data, (address, bytes32));
            bridgeNativeToRelay(to, requestId);
        } else if (action == uint32(IBridgeSettlerActions.BRIDGE_TO_LAYER_ZERO_OFT.selector)) {
            (IERC20 token, uint256 nativeFee, address oft, bytes memory sendData) = abi.decode(data, (IERC20, uint256, address, bytes));
            bridgeLayerZeroOFT(token, nativeFee, oft, sendData);
        } else if (action == uint32(IBridgeSettlerActions.UNDERPAYMENT_CHECK.selector)) {
            (uint256 msgValueMin) = abi.decode(data, (uint256));
            if (msg.value < msgValueMin) {
                assembly ("memory-safe") {
                    mstore(0x00, 0xd17e444b) // selector for `Underpayment(uint256,uint256)`
                    mstore(0x20, msgValueMin)
                    mstore(0x40, callvalue())
                    revert(0x1c, 0x44)
                }
            }
        } else {
            return false;
        }
        return true;
    }

    function _div512to256(uint512 n, uint512 d) internal view virtual override returns (uint256) {
        return n.div(d);
    }

    receive() external payable {}
}

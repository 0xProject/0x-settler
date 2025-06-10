// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {IERC721Owner} from "../IERC721Owner.sol";
import {DEPLOYER} from "../deployer/DeployerAddress.sol";
import {BridgeSettlerAbstract} from "./BridgeSettlerAbstract.sol";
import {IBridgeSettlerActions} from "./IBridgeSettlerActions.sol";
import {ALLOWANCE_HOLDER} from "../allowanceholder/IAllowanceHolder.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";

abstract contract BridgeSettlerBase is BridgeSettlerAbstract {
    using SafeTransferLib for IERC20;

    event GitCommit(bytes20 indexed);

    // TODO: Create script to deploy Bridge settler
    constructor(bytes20 gitCommit) {
        if (block.chainid != 31337) {
            emit GitCommit(gitCommit);
            assert(IERC721Owner(DEPLOYER).ownerOf(_tokenId()) == address(this));
        } else {
            assert(gitCommit == bytes20(0));
        }
    }

    function _dispatch(uint256, uint256 action, bytes calldata data) internal virtual override returns (bool) {
        if (action == uint32(IBridgeSettlerActions.SETTLER_SWAP.selector)) {
            (address token, uint256 amount, address settler, bytes memory settlerData) = abi.decode(data, (address, uint256, address, bytes));
            
            ALLOWANCE_HOLDER.exec(
                settler,
                token,
                amount,
                payable(settler),
                settlerData
            );
        } else if (action == uint32(IBridgeSettlerActions.BRIDGE.selector)) {
            (address token, address bridge, bytes memory bridgeData) = abi.decode(data, (address, address, bytes));

            uint256 balance = IERC20(token).fastBalanceOf(address(this));
            IERC20(token).approve(bridge, balance);
            (bool success, ) = bridge.call(bridgeData);
            if (!success) return false;
        } else {
            return false;
        }
        return true;
    }

    receive() external payable {}
}
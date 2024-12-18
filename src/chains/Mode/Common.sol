// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {SettlerBase} from "../../SettlerBase.sol";

import {FreeMemory} from "../../utils/FreeMemory.sol";

import {ISettlerActions} from "../../ISettlerActions.sol";
import {UnknownForkId} from "../../core/SettlerErrors.sol";

import {
    supSwapV3Factory,
    supSwapV3InitHash,
    supSwapV3ForkId,
    ISupSwapV3Callback
} from "../../core/univ3forks/SupSwapV3.sol";
import {kimFactory, kimInitHash, kimForkId} from "../../core/univ3forks/Kim.sol";
import {IAlgebraCallback} from "../../core/univ3forks/Algebra.sol";
import {swapModeV3Factory, swapModeV3InitHash, swapModeV3ForkId} from "../../core/univ3forks/SwapModeV3.sol";
import {IUniswapV3Callback} from "../../core/univ3forks/UniswapV3.sol";

import {DEPLOYER} from "../../deployer/DeployerAddress.sol";
import {MODE_SFS} from "./IModeSFS.sol";

// Solidity inheritance is stupid
import {Permit2PaymentAbstract} from "../../core/Permit2PaymentAbstract.sol";

abstract contract ModeMixin is FreeMemory, SettlerBase {
    constructor() {
        assert(block.chainid == 34443 || block.chainid == 31337);
        MODE_SFS.assign(MODE_SFS.getTokenId(DEPLOYER));
    }

    function _isRestrictedTarget(address target)
        internal
        pure
        virtual
        override(Permit2PaymentAbstract)
        returns (bool)
    {
        return target == address(MODE_SFS);
    }

    function _dispatch(uint256 i, uint256 action, bytes calldata data)
        internal
        virtual
        override(SettlerBase)
        DANGEROUS_freeMemory
        returns (bool)
    {
        return super._dispatch(i, action, data);
    }

    function _uniV3ForkInfo(uint8 forkId)
        internal
        pure
        override
        returns (address factory, bytes32 initHash, uint32 callbackSelector)
    {
        if (forkId == supSwapV3ForkId) {
            factory = supSwapV3Factory;
            initHash = supSwapV3InitHash;
            callbackSelector = uint32(ISupSwapV3Callback.supV3SwapCallback.selector);
        } else if (forkId == kimForkId) {
            factory = kimFactory;
            initHash = kimInitHash;
            callbackSelector = uint32(IAlgebraCallback.algebraSwapCallback.selector);
        } else if (forkId == swapModeV3ForkId) {
            factory = swapModeV3Factory;
            initHash = swapModeV3InitHash;
            callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
        } else {
            revert UnknownForkId(forkId);
        }
    }
}

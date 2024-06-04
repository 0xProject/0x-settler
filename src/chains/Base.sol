// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {SettlerBase} from "../SettlerBase.sol";
import {Settler} from "../Settler.sol";
import {SettlerMetaTxn} from "../SettlerMetaTxn.sol";

import {FreeMemory} from "../utils/FreeMemory.sol";

import {Velodrome, IVelodromePair} from "../core/Velodrome.sol";
import {ISettlerActions} from "../ISettlerActions.sol";
import {UnknownForkId} from "../core/SettlerErrors.sol";

import {uniswapV3BaseFactory, uniswapV3InitHash, IUniswapV3Callback} from "../core/univ3forks/UniswapV3.sol";
import {
    pancakeSwapV3Factory, pancakeSwapV3InitHash, IPancakeSwapV3Callback
} from "../core/univ3forks/PancakeSwapV3.sol";
import {sushiswapV3Factory, sushiswapV3InitHash} from "../core/univ3forks/SushiswapV3.sol";
import {aerodromeFactory, aerodromeInitHash} from "../core/univ3forks/AerodromeSlipstream.sol";
import {alienBaseV3Factory} from "../core/univ3forks/AlienBaseV3.sol";
import {baseXFactory} from "../core/univ3forks/BaseX.sol";

// Solidity inheritance is stupid
import {SettlerAbstract} from "../SettlerAbstract.sol";
import {AbstractContext} from "../Context.sol";
import {Permit2PaymentAbstract} from "../core/Permit2PaymentAbstract.sol";

abstract contract BaseMixin is FreeMemory, SettlerBase, Velodrome {
    constructor() {
        assert(block.chainid == 8453 || block.chainid == 31337);
    }

    function _dispatch(uint256 i, bytes4 action, bytes calldata data)
        internal
        virtual
        override
        DANGEROUS_freeMemory
        returns (bool)
    {
        if (super._dispatch(i, action, data)) {
            return true;
        } else if (action == ISettlerActions.VELODROME.selector) {
            (address recipient, uint256 bps, IVelodromePair pool, uint24 swapInfo, uint256 minAmountOut) =
                abi.decode(data, (address, uint256, IVelodromePair, uint24, uint256));

            sellToVelodrome(recipient, bps, pool, swapInfo, minAmountOut);
        } else {
            return false;
        }
        return true;
    }

    function _uniV3ForkInfo(uint8 forkId)
        internal
        pure
        override
        returns (address factory, bytes32 initHash, bytes4 callbackSelector)
    {
        if (forkId == 0) {
            factory = uniswapV3BaseFactory;
            initHash = uniswapV3InitHash;
            callbackSelector = IUniswapV3Callback.uniswapV3SwapCallback.selector;
        } else if (forkId == 1) {
            factory = pancakeSwapV3Factory;
            initHash = pancakeSwapV3InitHash;
            callbackSelector = IPancakeSwapV3Callback.pancakeV3SwapCallback.selector;
        } else if (forkId == 2) {
            factory = sushiswapV3Factory;
            initHash = sushiswapV3InitHash;
            callbackSelector = IUniswapV3Callback.uniswapV3SwapCallback.selector;
        } else if (forkId == 4) {
            factory = aerodromeFactory;
            initHash = aerodromeInitHash;
            callbackSelector = IUniswapV3Callback.uniswapV3SwapCallback.selector;
        } else if (forkId == 6) {
            factory = alienBaseV3Factory;
            initHash = uniswapV3InitHash;
            callbackSelector = IUniswapV3Callback.uniswapV3SwapCallback.selector;
        } else if (forkId == 7) {
            factory = baseXFactory;
            initHash = uniswapV3InitHash;
            callbackSelector = IUniswapV3Callback.uniswapV3SwapCallback.selector;
        } else {
            revert UnknownForkId(forkId);
        }
    }
}

/// @custom:security-contact security@0x.org
contract BaseSettler is Settler, BaseMixin {
    constructor(bytes20 gitCommit) SettlerBase(gitCommit) {}

    function _dispatchVIP(bytes4 action, bytes calldata data) internal override DANGEROUS_freeMemory returns (bool) {
        return super._dispatchVIP(action, data);
    }

    // Solidity inheritance is stupid
    function _isRestrictedTarget(address target)
        internal
        pure
        override(Settler, Permit2PaymentAbstract)
        returns (bool)
    {
        return super._isRestrictedTarget(target);
    }

    function _dispatch(uint256 i, bytes4 action, bytes calldata data)
        internal
        override(SettlerAbstract, SettlerBase, BaseMixin)
        returns (bool)
    {
        return super._dispatch(i, action, data);
    }

    function _msgSender() internal view override(Settler, AbstractContext) returns (address) {
        return super._msgSender();
    }
}

/// @custom:security-contact security@0x.org
contract BaseSettlerMetaTxn is SettlerMetaTxn, BaseMixin {
    constructor(bytes20 gitCommit) SettlerBase(gitCommit) {}

    function _dispatchVIP(bytes4 action, bytes calldata data, bytes calldata sig)
        internal
        override
        DANGEROUS_freeMemory
        returns (bool)
    {
        return super._dispatchVIP(action, data, sig);
    }

    // Solidity inheritance is stupid
    function _dispatch(uint256 i, bytes4 action, bytes calldata data)
        internal
        override(SettlerAbstract, SettlerBase, BaseMixin)
        returns (bool)
    {
        return super._dispatch(i, action, data);
    }

    function _msgSender() internal view override(SettlerMetaTxn, AbstractContext) returns (address) {
        return super._msgSender();
    }
}

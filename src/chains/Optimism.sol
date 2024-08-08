// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {SettlerBase} from "../SettlerBase.sol";
import {Settler} from "../Settler.sol";
import {SettlerMetaTxn} from "../SettlerMetaTxn.sol";

import {FreeMemory} from "../utils/FreeMemory.sol";

import {ISettlerActions} from "../ISettlerActions.sol";
import {UnknownForkId} from "../core/SettlerErrors.sol";

import {
    uniswapV3MainnetFactory,
    uniswapV3InitHash,
    uniswapV3ForkId,
    IUniswapV3Callback
} from "../core/univ3forks/UniswapV3.sol";
import {pancakeSwapV3InitHash, IPancakeSwapV3Callback} from "../core/univ3forks/PancakeSwapV3.sol";
import {sushiswapV3OptimismFactory, sushiswapV3ForkId} from "../core/univ3forks/SushiswapV3.sol";
import {velodromeFactory, velodromeInitHash, velodromeForkId} from "../core/univ3forks/VelodromeSlipstream.sol";
import {
    solidlyV3Factory, solidlyV3InitHash, solidlyV3ForkId, ISolidlyV3Callback
} from "../core/univ3forks/SolidlyV3.sol";
import {dackieSwapV3OptimismFactory, dackieSwapV3ForkId} from "../core/univ3forks/DackieSwapV3.sol";

// Solidity inheritance is stupid
import {SettlerAbstract} from "../SettlerAbstract.sol";
import {AbstractContext} from "../Context.sol";
import {Permit2PaymentAbstract} from "../core/Permit2PaymentAbstract.sol";

abstract contract OptimismMixin is FreeMemory, SettlerBase {
    constructor() {
        assert(block.chainid == 10 || block.chainid == 31337);
    }

    function _dispatch(uint256 i, bytes4 action, bytes calldata data)
        internal
        virtual
        override
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
        if (forkId == uniswapV3ForkId) {
            factory = uniswapV3MainnetFactory;
            initHash = uniswapV3InitHash;
            callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
        } else if (forkId == sushiswapV3ForkId) {
            factory = sushiswapV3OptimismFactory;
            initHash = uniswapV3InitHash;
            callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
        } else if (forkId == solidlyV3ForkId) {
            factory = solidlyV3Factory;
            initHash = solidlyV3InitHash;
            callbackSelector = uint32(ISolidlyV3Callback.solidlyV3SwapCallback.selector);
        } else if (forkId == velodromeForkId) {
            factory = velodromeFactory;
            initHash = velodromeInitHash;
            callbackSelector = uint32(IUniswapV3Callback.uniswapV3SwapCallback.selector);
        } else if (forkId == dackieSwapV3ForkId) {
            factory = dackieSwapV3OptimismFactory;
            initHash = pancakeSwapV3InitHash;
            callbackSelector = uint32(IPancakeSwapV3Callback.pancakeV3SwapCallback.selector);
        } else {
            revert UnknownForkId(forkId);
        }
    }
}

/// @custom:security-contact security@0x.org
contract OptimismSettler is Settler, OptimismMixin {
    constructor(bytes20 gitCommit) Settler(gitCommit) {}

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
        override(SettlerAbstract, SettlerBase, OptimismMixin)
        returns (bool)
    {
        return super._dispatch(i, action, data);
    }

    function _msgSender() internal view override(Settler, AbstractContext) returns (address) {
        return super._msgSender();
    }
}

/// @custom:security-contact security@0x.org
contract OptimismSettlerMetaTxn is SettlerMetaTxn, OptimismMixin {
    constructor(bytes20 gitCommit) SettlerMetaTxn(gitCommit) {}

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
        override(SettlerAbstract, SettlerBase, OptimismMixin)
        returns (bool)
    {
        return super._dispatch(i, action, data);
    }

    function _msgSender() internal view override(SettlerMetaTxn, AbstractContext) returns (address) {
        return super._msgSender();
    }
}

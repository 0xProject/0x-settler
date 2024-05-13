// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {SettlerBase} from "../SettlerBase.sol";
import {Settler} from "../Settler.sol";
import {SettlerMetaTxn} from "../SettlerMetaTxn.sol";

import {IPSM, MakerPSM} from "../core/MakerPSM.sol";
import {ActionInvalid} from "../core/SettlerErrors.sol";

import {IERC20Meta} from "../IERC20.sol";
import {ISettlerActions} from "../ISettlerActions.sol";
import {ActionInvalid, UnknownForkId} from "../core/SettlerErrors.sol";

import {uniswapV3MainnetFactory, uniswapV3InitHash, IUniswapV3Callback} from "../core/univ3forks/UniswapV3.sol";
import {
    pancakeSwapV3Factory, pancakeSwapV3InitHash, IPancakeSwapV3Callback
} from "../core/univ3forks/PancakeSwapV3.sol";
import {solidlyV3Factory, solidlyV3InitHash, ISolidlyV3Callback} from "../core/univ3forks/SolidlyV3.sol";

// Solidity inheritance is stupid
import {AbstractContext} from "../Context.sol";
import {Permit2PaymentBase} from "../core/Permit2Payment.sol";
import {Permit2PaymentAbstract} from "../core/Permit2PaymentAbstract.sol";

abstract contract MainnetMixin is MakerPSM, SettlerBase {
    constructor() MakerPSM(0x6B175474E89094C44Da98b954EedeAC495271d0F) {
        assert(block.chainid == 1 || block.chainid == 31337);
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
        } else if (action == ISettlerActions.MAKERPSM_SELL.selector) {
            (address recipient, uint256 bps, IPSM psm, IERC20Meta gemToken) =
                abi.decode(data, (address, uint256, IPSM, IERC20Meta));

            makerPsmSellGem(recipient, bps, psm, gemToken);
        } else if (action == ISettlerActions.MAKERPSM_BUY.selector) {
            (address recipient, uint256 bps, IPSM psm, IERC20Meta gemToken) =
                abi.decode(data, (address, uint256, IPSM, IERC20Meta));

            makerPsmBuyGem(recipient, bps, psm, gemToken);
        } else {
            revert ActionInvalid(i, action, data);
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
            factory = uniswapV3MainnetFactory;
            initHash = uniswapV3InitHash;
            callbackSelector = IUniswapV3Callback.uniswapV3SwapCallback.selector;
        } else if (forkId == 1) {
            factory = pancakeSwapV3Factory;
            initHash = pancakeSwapV3InitHash;
            callbackSelector = IPancakeSwapV3Callback.pancakeV3SwapCallback.selector;
        } else if (forkId == 2) {
            factory = solidlyV3Factory;
            initHash = solidlyV3InitHash;
            callbackSelector = ISolidlyV3Callback.solidlyV3SwapCallback.selector;
        } else {
            revert UnknownForkId(forkId);
        }
    }
}

/// @custom:security-contact security@0x.org
contract MainnetSettler is Settler, MainnetMixin {
    // Solidity inheritance is stupid
    function _isRestrictedTarget(address target)
        internal
        pure
        override(Settler, Permit2PaymentBase, Permit2PaymentAbstract)
        returns (bool)
    {
        return super._isRestrictedTarget(target);
    }

    function _dispatch(uint256 i, bytes4 action, bytes calldata data)
        internal
        override(SettlerBase, MainnetMixin)
        returns (bool)
    {
        return super._dispatch(i, action, data);
    }

    function _msgSender() internal view override(Settler, Permit2PaymentBase, AbstractContext) returns (address) {
        return super._msgSender();
    }
}

/// @custom:security-contact security@0x.org
contract MainnetSettlerMetaTxn is SettlerMetaTxn, MainnetMixin {
    // Solidity inheritance is stupid
    function _dispatch(uint256 i, bytes4 action, bytes calldata data)
        internal
        override(SettlerBase, MainnetMixin)
        returns (bool)
    {
        return super._dispatch(i, action, data);
    }

    function _msgSender()
        internal
        view
        override(SettlerMetaTxn, Permit2PaymentBase, AbstractContext)
        returns (address)
    {
        return super._msgSender();
    }
}

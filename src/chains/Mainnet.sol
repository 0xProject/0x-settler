// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {SettlerBase} from "../SettlerBase.sol";
import {Settler} from "../Settler.sol";
import {SettlerMetaTxn} from "../SettlerMetaTxn.sol";

import {CurveTricrypto} from "../core/CurveTricrypto.sol";
import {DodoV1} from "../core/DodoV1.sol";
import {FreeMemory} from "../utils/FreeMemory.sol";

import {ISettlerActions} from "../ISettlerActions.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {IERC20} from "../IERC20.sol";
import {UnknownForkId} from "../core/SettlerErrors.sol";

import {
    uniswapV3MainnetFactory,
    uniswapV3InitHash,
    uniswapV3ForkId,
    IUniswapV3Callback
} from "../core/univ3forks/UniswapV3.sol";
import {
    pancakeSwapV3Factory,
    pancakeSwapV3InitHash,
    pancakeSwapV3ForkId,
    IPancakeSwapV3Callback
} from "../core/univ3forks/PancakeSwapV3.sol";
import {
    solidlyV3Factory, solidlyV3InitHash, solidlyV3ForkId, ISolidlyV3Callback
} from "../core/univ3forks/SolidlyV3.sol";

// Solidity inheritance is stupid
import {SettlerAbstract} from "../SettlerAbstract.sol";
import {AbstractContext} from "../Context.sol";
import {Permit2PaymentAbstract} from "../core/Permit2PaymentAbstract.sol";

abstract contract MainnetMixin is FreeMemory, SettlerBase, CurveTricrypto, DodoV1 {
    constructor() {
        assert(block.chainid == 1 || block.chainid == 31337);
    }

    function _dispatch(uint256 i, bytes4 action, bytes calldata data)
        internal
        virtual
        override(SettlerAbstract, SettlerBase)
        DANGEROUS_freeMemory
        returns (bool)
    {
        if (super._dispatch(i, action, data)) {
            return true;
        } else if (action == ISettlerActions.MAKERPSM.selector) {
            revert("unimplemented");
        } else if (action == ISettlerActions.DODOV1.selector) {
            (IERC20 sellToken, uint256 bps, address dodo, bool quoteForBase, uint256 minBuyAmount) =
                abi.decode(data, (IERC20, uint256, address, bool, uint256));

            sellToDodoV1(sellToken, bps, dodo, quoteForBase, minBuyAmount);
        } else {
            return false;
        }
        return true; // this is unreachable due to non-Cancun-related refactors
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
        } else if (forkId == pancakeSwapV3ForkId) {
            factory = pancakeSwapV3Factory;
            initHash = pancakeSwapV3InitHash;
            callbackSelector = uint32(IPancakeSwapV3Callback.pancakeV3SwapCallback.selector);
        } else if (forkId == solidlyV3ForkId) {
            factory = solidlyV3Factory;
            initHash = solidlyV3InitHash;
            callbackSelector = uint32(ISolidlyV3Callback.solidlyV3SwapCallback.selector);
        } else {
            revert UnknownForkId(forkId);
        }
    }

    function _curveFactory() internal pure override returns (address) {
        return 0x0c0e5f2fF0ff18a3be9b835635039256dC4B4963;
    }
}

/// @custom:security-contact security@0x.org
contract MainnetSettler is Settler, MainnetMixin {
    constructor(bytes20 gitCommit) SettlerBase(gitCommit) {}

    function _dispatchVIP(bytes4 action, bytes calldata data) internal override DANGEROUS_freeMemory returns (bool) {
        if (super._dispatchVIP(action, data)) {
            return true;
        } else if (action == ISettlerActions.CURVE_TRICRYPTO_VIP.selector) {
            (
                address recipient,
                uint80 poolInfo,
                ISignatureTransfer.PermitTransferFrom memory permit,
                bytes memory sig,
                uint256 minBuyAmount
            ) = abi.decode(data, (address, uint80, ISignatureTransfer.PermitTransferFrom, bytes, uint256));

            sellToCurveTricryptoVIP(recipient, poolInfo, permit, sig, minBuyAmount);
        } else {
            return false;
        }
        return true;
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
        override(SettlerAbstract, SettlerBase, MainnetMixin)
        returns (bool)
    {
        return super._dispatch(i, action, data);
    }

    function _msgSender() internal view override(Settler, AbstractContext) returns (address) {
        return super._msgSender();
    }
}

/// @custom:security-contact security@0x.org
contract MainnetSettlerMetaTxn is SettlerMetaTxn, MainnetMixin {
    constructor(bytes20 gitCommit) SettlerBase(gitCommit) {}

    function _dispatchVIP(bytes4 action, bytes calldata data, bytes calldata sig)
        internal
        override
        DANGEROUS_freeMemory
        returns (bool)
    {
        if (super._dispatchVIP(action, data, sig)) {
            return true;
        } else if (action == ISettlerActions.METATXN_CURVE_TRICRYPTO_VIP.selector) {
            (
                address recipient,
                uint80 poolInfo,
                ISignatureTransfer.PermitTransferFrom memory permit,
                uint256 minBuyAmount
            ) = abi.decode(data, (address, uint80, ISignatureTransfer.PermitTransferFrom, uint256));

            sellToCurveTricryptoVIP(recipient, poolInfo, permit, sig, minBuyAmount);
        } else {
            return false;
        }
        return true;
    }

    // Solidity inheritance is stupid
    function _dispatch(uint256 i, bytes4 action, bytes calldata data)
        internal
        override(SettlerAbstract, SettlerBase, MainnetMixin)
        returns (bool)
    {
        return super._dispatch(i, action, data);
    }

    function _msgSender() internal view override(SettlerMetaTxn, AbstractContext) returns (address) {
        return super._msgSender();
    }
}

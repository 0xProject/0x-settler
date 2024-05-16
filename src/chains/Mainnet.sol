// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {SettlerBase} from "../SettlerBase.sol";
import {Settler} from "../Settler.sol";
import {SettlerMetaTxn} from "../SettlerMetaTxn.sol";

import {IERC20, IERC20Meta} from "../IERC20.sol";
import {IPSM, MakerPSM} from "../core/MakerPSM.sol";
import {CurveTricrypto} from "../core/CurveTricrypto.sol";
import {DodoV1} from "../core/DodoV1.sol";
import {FreeMemory} from "../utils/FreeMemory.sol";

import {ISettlerActions} from "../ISettlerActions.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {UnknownForkId} from "../core/SettlerErrors.sol";

import {uniswapV3MainnetFactory, uniswapV3InitHash, IUniswapV3Callback} from "../core/univ3forks/UniswapV3.sol";
import {
    pancakeSwapV3Factory, pancakeSwapV3InitHash, IPancakeSwapV3Callback
} from "../core/univ3forks/PancakeSwapV3.sol";
import {solidlyV3Factory, solidlyV3InitHash, ISolidlyV3Callback} from "../core/univ3forks/SolidlyV3.sol";

// Solidity inheritance is stupid
import {SettlerAbstract} from "../SettlerAbstract.sol";
import {AbstractContext} from "../Context.sol";
import {Permit2PaymentBase} from "../core/Permit2Payment.sol";
import {Permit2PaymentAbstract} from "../core/Permit2PaymentAbstract.sol";

abstract contract MainnetMixin is FreeMemory, SettlerBase, MakerPSM, CurveTricrypto, DodoV1 {
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
        } else if (action == ISettlerActions.MAKERPSM_SELL.selector) {
            (address recipient, IERC20Meta gemToken, uint256 bps, IPSM psm) =
                abi.decode(data, (address, IERC20Meta, uint256, IPSM));

            makerPsmSellGem(recipient, gemToken, bps, psm);
        } else if (action == ISettlerActions.MAKERPSM_BUY.selector) {
            (address recipient, IERC20Meta gemToken, uint256 bps, IPSM psm) =
                abi.decode(data, (address, IERC20Meta, uint256, IPSM));

            makerPsmBuyGem(recipient, gemToken, bps, psm);
        } else if (action == ISettlerActions.DODOV1.selector) {
            (IERC20 sellToken, uint256 bps, address dodo, bool quoteForBase, uint256 minBuyAmount) =
                abi.decode(data, (IERC20, uint256, address, bool, uint256));

            sellToDodoV1(sellToken, bps, dodo, quoteForBase, minBuyAmount);
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
        } else if (action == ISettlerActions.DODOV1_VIP.selector) {
            /*
            (
                uint64 deployerNonce,
                ISignatureTransfer.PermitTransferFrom memory permit,
                bytes memory sig,
                bool quoteForBase,
                uint256 minBuyAmount
            ) = abi.decode(data, (uint64, ISignatureTransfer.PermitTransferFrom, bytes, bool, uint256));

            sellToDodoV1VIP(deployerNonce, permit, sig, quoteForBase, minBuyAmount);
            */
            revert("unimplemented");
        } else {
            return false;
        }
        return true;
    }

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
        } else if (action == ISettlerActions.METATXN_DODOV1_VIP.selector) {
            /*
            (
                uint64 deployerNonce,
                ISignatureTransfer.PermitTransferFrom memory permit,
                bool quoteForBase,
                uint256 minBuyAmount
            ) = abi.decode(data, (uint64, ISignatureTransfer.PermitTransferFrom, bool, uint256));

            sellToDodoV1VIP(deployerNonce, permit, sig, quoteForBase, minBuyAmount);
            */
            revert("unimplemented");
        } else {
            return false;
        }
        return true;
    }

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

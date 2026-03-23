// SPDX-License-Identifier: MIT
pragma solidity =0.8.33;

import {ArbitrumMixin} from "./Common.sol";
import {SettlerMetaTxn} from "../../SettlerMetaTxn.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ISettlerActions} from "../../ISettlerActions.sol";

// Solidity inheritance is stupid
import {SettlerBase} from "../../SettlerBase.sol";
import {AbstractContext} from "../../Context.sol";
import {Permit2PaymentAbstract} from "../../core/Permit2PaymentAbstract.sol";

/// @custom:security-contact security@0x.org
contract ArbitrumSettlerMetaTxn is SettlerMetaTxn, ArbitrumMixin {
    constructor(bytes20 gitCommit) SettlerBase(gitCommit) {}

    function _dispatchVIP(uint256 action, bytes calldata data, bytes calldata sig, AllowedSlippage memory slippage)
        internal
        virtual
        override
        DANGEROUS_freeMemory
        returns (bool)
    {
        if (super._dispatchVIP(action, data, sig, slippage)) {
            return true;
        } else if (action == uint32(ISettlerActions.METATXN_UNISWAPV4_VIP.selector)) {
            (
                address payable recipient,
                ISignatureTransfer.PermitTransferFrom memory permit,
                bool feeOnTransfer,
                uint256 hashMul,
                uint256 hashMod,
                bytes memory fills,
                uint256 minAmountOut
            ) = abi.decode(
                data, (address, ISignatureTransfer.PermitTransferFrom, bool, uint256, uint256, bytes, uint256)
            );
            IERC20 buyToken;
            (recipient, buyToken, minAmountOut) = _maybeSetSlippage(slippage, recipient, minAmountOut);
            (IERC20 actualBuyToken, uint256 actualAmountOut) =
                sellToUniswapV4VIP(recipient, feeOnTransfer, hashMul, hashMod, fills, permit, sig);
            _checkSlippage(buyToken, minAmountOut, actualBuyToken, actualAmountOut);
        } else if (action == uint32(ISettlerActions.METATXN_BALANCERV3_VIP.selector)) {
            (
                address payable recipient,
                ISignatureTransfer.PermitTransferFrom memory permit,
                bool feeOnTransfer,
                uint256 hashMul,
                uint256 hashMod,
                bytes memory fills,
                uint256 minAmountOut
            ) = abi.decode(
                data, (address, ISignatureTransfer.PermitTransferFrom, bool, uint256, uint256, bytes, uint256)
            );
            IERC20 buyToken;
            (recipient, buyToken, minAmountOut) = _maybeSetSlippage(slippage, recipient, minAmountOut);
            (IERC20 actualBuyToken, uint256 actualAmountOut) =
                sellToBalancerV3VIP(recipient, feeOnTransfer, hashMul, hashMod, fills, permit, sig);
            _checkSlippage(buyToken, minAmountOut, actualBuyToken, actualAmountOut);
        } else if (action == uint32(ISettlerActions.METATXN_MAVERICKV2_VIP.selector)) {
            (
                address payable recipient,
                ISignatureTransfer.PermitTransferFrom memory permit,
                bytes32 salt,
                bool tokenAIn,
                int32 tickLimit,
                uint256 minAmountOut
            ) = abi.decode(data, (address, ISignatureTransfer.PermitTransferFrom, bytes32, bool, int32, uint256));
            IERC20 buyToken;
            (recipient, buyToken, minAmountOut) = _maybeSetSlippage(slippage, recipient, minAmountOut);
            (IERC20 actualBuyToken, uint256 actualAmountOut) =
                sellToMaverickV2VIP(recipient, salt, tokenAIn, permit, sig, tickLimit);
            _checkSlippage(buyToken, minAmountOut, actualBuyToken, actualAmountOut);
        } else if (action == uint32(ISettlerActions.METATXN_CURVE_TRICRYPTO_VIP.selector)) {
            (
                address payable recipient,
                ISignatureTransfer.PermitTransferFrom memory permit,
                uint80 poolInfo,
                uint256 minAmountOut
            ) = abi.decode(data, (address, ISignatureTransfer.PermitTransferFrom, uint80, uint256));
            IERC20 buyToken;
            (recipient, buyToken, minAmountOut) = _maybeSetSlippage(slippage, recipient, minAmountOut);
            (IERC20 actualBuyToken, uint256 actualAmountOut) = sellToCurveTricryptoVIP(recipient, poolInfo, permit, sig);
            _checkSlippage(buyToken, minAmountOut, actualBuyToken, actualAmountOut);
        } else {
            return false;
        }
        return true;
    }

    // Solidity inheritance is stupid
    function _dispatch(uint256 i, uint256 action, bytes calldata data, AllowedSlippage memory slippage)
        internal
        virtual
        override(SettlerBase, ArbitrumMixin)
        returns (bool)
    {
        return super._dispatch(i, action, data, slippage);
    }

    function _isRestrictedTarget(address target)
        internal
        view
        virtual
        override(SettlerMetaTxn, ArbitrumMixin)
        returns (bool)
    {
        return super._isRestrictedTarget(target);
    }

    function _msgSender() internal view virtual override(SettlerMetaTxn, AbstractContext) returns (address) {
        return super._msgSender();
    }

    function _fallback(bytes calldata data)
        internal
        virtual
        override(Permit2PaymentAbstract, ArbitrumMixin)
        returns (bool, bytes memory)
    {
        return super._fallback(data);
    }
}

// SPDX-License-Identifier: MIT
pragma solidity =0.8.34;

import {MainnetMixin, MainnetCommon} from "./Common.sol";
import {Settler} from "../../Settler.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ISettlerActions} from "../../ISettlerActions.sol";

import {FastLogic} from "../../utils/FastLogic.sol";

// Solidity inheritance is stupid
import {SettlerBase} from "../../SettlerBase.sol";
import {Permit2PaymentAbstract} from "../../core/Permit2PaymentAbstract.sol";
import {AbstractContext} from "../../Context.sol";

// The taker dispatcher must precede the chain dispatcher so candidates retain its checks.
/// @custom:security-contact security@0x.org
contract MainnetSettler is MainnetMixin, Settler, MainnetCommon {
    using FastLogic for bool;

    constructor(bytes20 gitCommit) SettlerBase(gitCommit) {}

    function _dispatch(uint256 i, uint256 action, bytes calldata data, AllowedSlippage memory slippage)
        internal
        override(Settler, MainnetMixin, MainnetCommon)
        returns (bool)
    {
        return super._dispatch(i, action, data, slippage);
    }

    function _dispatchVIP(uint256 action, bytes calldata data) internal override DANGEROUS_freeMemory returns (bool) {
        if (super._dispatchVIP(action, data)) {
            return true;
        } else if (action == uint32(ISettlerActions.UNISWAPV4_VIP.selector)) {
            (
                address recipient,
                ISignatureTransfer.PermitTransferFrom memory permit,
                uint8 forkId,
                bool feeOnTransfer,
                uint256 hashMul,
                uint256 hashMod,
                bytes memory fills,
                bytes memory sig,
                uint256 amountOutMin
            ) = abi.decode(
                data,
                (address, ISignatureTransfer.PermitTransferFrom, uint8, bool, uint256, uint256, bytes, bytes, uint256)
            );

            sellToUniswapV4VIP(recipient, forkId, feeOnTransfer, hashMul, hashMod, fills, permit, sig, amountOutMin);
        } else if ((action == uint32(ISettlerActions.BALANCERV3_VIP.selector))
                .or(action == uint32(ISettlerActions.EKUBOV3_VIP.selector))) {
            (
                address recipient,
                ISignatureTransfer.PermitTransferFrom memory permit,
                bool feeOnTransfer,
                uint256 hashMul,
                uint256 hashMod,
                bytes memory fills,
                bytes memory sig,
                uint256 amountOutMin
            ) = abi.decode(
                data, (address, ISignatureTransfer.PermitTransferFrom, bool, uint256, uint256, bytes, bytes, uint256)
            );

            if (action == uint32(ISettlerActions.BALANCERV3_VIP.selector)) {
                sellToBalancerV3VIP(recipient, feeOnTransfer, hashMul, hashMod, fills, permit, sig, amountOutMin);
            } else { // if (action == uint32(ISettlerActions.EKUBOV3_VIP.selector))
                sellToEkuboV3VIP(recipient, feeOnTransfer, hashMul, hashMod, fills, permit, sig, amountOutMin);
            }
        } /* else if (action == uint32(ISettlerActions.CURVE_TRICRYPTO_VIP.selector)) {
            (
                address recipient,
                ISignatureTransfer.PermitTransferFrom memory permit,
                uint80 poolInfo,
                bytes memory sig,
                uint256 minBuyAmount
            ) = abi.decode(data, (address, ISignatureTransfer.PermitTransferFrom, uint80, bytes, uint256));
            sellToCurveTricryptoVIP(recipient, poolInfo, permit, sig, minBuyAmount);
        } */ else {
            return false;
        }
        return true;
    }

    // Solidity inheritance is stupid
    function _isRestrictedTarget(address target)
        internal
        view
        override(Settler, MainnetMixin, MainnetCommon)
        returns (bool)
    {
        return super._isRestrictedTarget(target);
    }

    function _msgSender() internal view override(Settler, AbstractContext) returns (address) {
        return super._msgSender();
    }

    function _fallback(bytes calldata data)
        internal
        virtual
        override(Permit2PaymentAbstract, MainnetMixin, MainnetCommon)
        returns (bool, bytes memory)
    {
        return super._fallback(data);
    }
}

// SPDX-License-Identifier: MIT
pragma solidity =0.8.25;

import {MainnetMixin} from "./Common.sol";
import {Settler} from "../../Settler.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ISettlerActions} from "../../ISettlerActions.sol";

// Solidity inheritance is stupid
import {SettlerAbstract} from "../../SettlerAbstract.sol";
import {SettlerBase} from "../../SettlerBase.sol";
import {Permit2PaymentAbstract} from "../../core/Permit2PaymentAbstract.sol";
import {AbstractContext} from "../../Context.sol";

/// @custom:security-contact security@0x.org
contract MainnetSettler is Settler, MainnetMixin {
    constructor(bytes20 gitCommit) SettlerBase(gitCommit) {}

    function _dispatchVIP(uint256 action, bytes calldata data) internal override DANGEROUS_freeMemory returns (bool) {
        if (super._dispatchVIP(action, data)) {
            return true;
        } else if (action == uint32(ISettlerActions.UNISWAPV4_VIP.selector)) {
            (
                address recipient,
                bool feeOnTransfer,
                uint256 hashMul,
                uint256 hashMod,
                bytes memory fills,
                ISignatureTransfer.PermitTransferFrom memory permit,
                bytes memory sig,
                uint256 amountOutMin
            ) = abi.decode(
                data, (address, bool, uint256, uint256, bytes, ISignatureTransfer.PermitTransferFrom, bytes, uint256)
            );

            sellToUniswapV4VIP(recipient, feeOnTransfer, hashMul, hashMod, fills, permit, sig, amountOutMin);
        } else if (action == uint32(ISettlerActions.MAVERICKV2_VIP.selector)) {
            (
                address recipient,
                bytes32 salt,
                bool tokenAIn,
                ISignatureTransfer.PermitTransferFrom memory permit,
                bytes memory sig,
                uint256 minBuyAmount
            ) = abi.decode(data, (address, bytes32, bool, ISignatureTransfer.PermitTransferFrom, bytes, uint256));

            sellToMaverickV2VIP(recipient, salt, tokenAIn, permit, sig, minBuyAmount);
        } else if (action == uint32(ISettlerActions.CURVE_TRICRYPTO_VIP.selector)) {
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
    function _dispatch(uint256 action, bytes calldata data)
        internal
        override(SettlerAbstract, SettlerBase, MainnetMixin)
        returns (bool)
    {
        return super._dispatch(action, data);
    }
}

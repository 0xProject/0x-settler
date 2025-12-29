// SPDX-License-Identifier: MIT
pragma solidity =0.8.33;

import {BaseMixin} from "./Common.sol";
import {Settler} from "../../Settler.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ISettlerActions} from "../../ISettlerActions.sol";

// Solidity inheritance is stupid
import {SettlerAbstract} from "../../SettlerAbstract.sol";
import {SettlerBase} from "../../SettlerBase.sol";
import {AbstractContext} from "../../Context.sol";
import {Permit2Payment} from "../../core/Permit2Payment.sol";

/// @custom:security-contact security@0x.org
contract BaseSettler is Settler, BaseMixin {
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
        } else if (action == uint32(ISettlerActions.BALANCERV3_VIP.selector)) {
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

            sellToBalancerV3VIP(recipient, feeOnTransfer, hashMul, hashMod, fills, permit, sig, amountOutMin);
        } else if (action == uint32(ISettlerActions.MAVERICKV2_VIP.selector)) {
            (
                address recipient,
                bytes32 salt,
                bool tokenAIn,
                ISignatureTransfer.PermitTransferFrom memory permit,
                bytes memory sig,
                int32 tickLimit,
                uint256 minBuyAmount
            ) = abi.decode(data, (address, bytes32, bool, ISignatureTransfer.PermitTransferFrom, bytes, int32, uint256));

            sellToMaverickV2VIP(recipient, salt, tokenAIn, permit, sig, tickLimit, minBuyAmount);
        } else if (action == uint32(ISettlerActions.PANCAKE_INFINITY_VIP.selector)) {
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

            sellToPancakeInfinityVIP(recipient, feeOnTransfer, hashMul, hashMod, fills, permit, sig, amountOutMin);
        } else {
            return false;
        }
        return true;
    }

    // Solidity inheritance is stupid
    function _isRestrictedTarget(address target)
        internal
        view
        override(Settler, BaseMixin)
        returns (bool)
    {
        return super._isRestrictedTarget(target);
    }

    function _dispatch(uint256 i, uint256 action, bytes calldata data)
        internal
        override(Settler, BaseMixin)
        returns (bool)
    {
        return super._dispatch(i, action, data);
    }

    function _msgSender() internal view override(Settler, AbstractContext) returns (address) {
        return super._msgSender();
    }

    function _chainSpecificFallback(bytes calldata data)
        internal
        view
        virtual
        override(Permit2Payment, BaseMixin)
        returns (bytes memory)
    {
        return BaseMixin._chainSpecificFallback(data);
    }
}

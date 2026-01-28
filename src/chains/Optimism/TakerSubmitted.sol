// SPDX-License-Identifier: MIT
pragma solidity =0.8.25;

import {OptimismMixin} from "./Common.sol";
import {Settler} from "../../Settler.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ISettlerActions} from "../../ISettlerActions.sol";

// Solidity inheritance is stupid
import {SettlerAbstract} from "../../SettlerAbstract.sol";
import {SettlerBase} from "../../SettlerBase.sol";
import {AbstractContext} from "../../Context.sol";
import {Permit2PaymentAbstract} from "../../core/Permit2PaymentAbstract.sol";

/// @custom:security-contact security@0x.org
contract OptimismSettler is Settler, OptimismMixin {
    constructor(bytes20 gitCommit) SettlerBase(gitCommit) {}

    function _dispatchVIP(uint256 action, bytes calldata data) internal override DANGEROUS_freeMemory returns (bool) {
        if (super._dispatchVIP(action, data)) {
            return true;
        } else if (action == uint32(ISettlerActions.UNISWAPV4_VIP.selector)) {
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

            sellToUniswapV4VIP(recipient, feeOnTransfer, hashMul, hashMod, fills, permit, sig, amountOutMin);
        } else if (action == uint32(ISettlerActions.BALANCERV3_VIP.selector)) {
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

            sellToBalancerV3VIP(recipient, feeOnTransfer, hashMul, hashMod, fills, permit, sig, amountOutMin);
        } else {
            return false;
        }
        return true;
    }

    // Solidity inheritance is stupid
    function _isRestrictedTarget(address target)
        internal
        view
        override(Settler, OptimismMixin)
        returns (bool)
    {
        return super._isRestrictedTarget(target);
    }

    function _dispatch(uint256 i, uint256 action, bytes calldata data)
        internal
        override(Settler, OptimismMixin)
        returns (bool)
    {
        return super._dispatch(i, action, data);
    }

    function _msgSender() internal view override(Settler, AbstractContext) returns (address) {
        return super._msgSender();
    }

    function _fallback(bytes calldata data)
        internal
        virtual
        override(Permit2PaymentAbstract, OptimismMixin)
        returns (bool, bytes memory)
    {
        return super._fallback(data);
    }
}

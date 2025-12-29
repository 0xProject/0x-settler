// SPDX-License-Identifier: MIT
pragma solidity =0.8.33;

import {BnbMixin} from "./Common.sol";
import {SettlerMetaTxn} from "../../SettlerMetaTxn.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ISettlerActions} from "../../ISettlerActions.sol";

// Solidity inheritance is stupid
import {SettlerAbstract} from "../../SettlerAbstract.sol";
import {SettlerBase} from "../../SettlerBase.sol";
import {AbstractContext} from "../../Context.sol";
import {Permit2PaymentBase} from "../../core/Permit2Payment.sol";

/// @custom:security-contact security@0x.org
contract BnbSettlerMetaTxn is SettlerMetaTxn, BnbMixin {
    constructor(bytes20 gitCommit) SettlerBase(gitCommit) {}

    function _dispatchVIP(uint256 action, bytes calldata data, bytes calldata sig)
        internal
        virtual
        override
        DANGEROUS_freeMemory
        returns (bool)
    {
        if (super._dispatchVIP(action, data, sig)) {
            return true;
        } else if (action == uint32(ISettlerActions.METATXN_UNISWAPV4_VIP.selector)) {
            (
                address recipient,
                bool feeOnTransfer,
                uint256 hashMul,
                uint256 hashMod,
                bytes memory fills,
                ISignatureTransfer.PermitTransferFrom memory permit,
                uint256 amountOutMin
            ) = abi.decode(
                data, (address, bool, uint256, uint256, bytes, ISignatureTransfer.PermitTransferFrom, uint256)
            );

            sellToUniswapV4VIP(recipient, feeOnTransfer, hashMul, hashMod, fills, permit, sig, amountOutMin);
        } else if (action == uint32(ISettlerActions.METATXN_MAVERICKV2_VIP.selector)) {
            (
                address recipient,
                bytes32 salt,
                bool tokenAIn,
                ISignatureTransfer.PermitTransferFrom memory permit,
                int32 tickLimit,
                uint256 minBuyAmount
            ) = abi.decode(data, (address, bytes32, bool, ISignatureTransfer.PermitTransferFrom, int32, uint256));

            sellToMaverickV2VIP(recipient, salt, tokenAIn, permit, sig, tickLimit, minBuyAmount);
        } else if (action == uint32(ISettlerActions.METATXN_PANCAKE_INFINITY_VIP.selector)) {
            (
                address recipient,
                bool feeOnTransfer,
                uint256 hashMul,
                uint256 hashMod,
                bytes memory fills,
                ISignatureTransfer.PermitTransferFrom memory permit,
                uint256 amountOutMin
            ) = abi.decode(
                data, (address, bool, uint256, uint256, bytes, ISignatureTransfer.PermitTransferFrom, uint256)
            );

            sellToPancakeInfinityVIP(recipient, feeOnTransfer, hashMul, hashMod, fills, permit, sig, amountOutMin);
        } else {
            return false;
        }
        return true;
    }

    // Solidity inheritance is stupid
    function _dispatch(uint256 i, uint256 action, bytes calldata data)
        internal
        virtual
        override(SettlerAbstract, SettlerBase, BnbMixin)
        returns (bool)
    {
        return super._dispatch(i, action, data);
    }

    function _isRestrictedTarget(address target)
        internal
        view
        virtual
        override(SettlerMetaTxn, BnbMixin)
        returns (bool)
    {
        return super._isRestrictedTarget(target);
    }

    function _msgSender() internal view virtual override(SettlerMetaTxn, AbstractContext) returns (address) {
        return super._msgSender();
    }
}

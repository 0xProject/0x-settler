// SPDX-License-Identifier: MIT
pragma solidity =0.8.34;

import {PolygonMixin} from "./Common.sol";
import {Settler} from "../../Settler.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ISettlerActions} from "../../ISettlerActions.sol";

// Solidity inheritance is stupid
import {SettlerAbstract} from "../../SettlerAbstract.sol";
import {SettlerBase} from "../../SettlerBase.sol";
import {AbstractContext} from "../../Context.sol";
import {Permit2PaymentAbstract} from "../../core/Permit2PaymentAbstract.sol";
import {Permit} from "../../core/Permit.sol";
import {Panic} from "../../utils/Panic.sol";

/// @custom:security-contact security@0x.org
contract PolygonSettler is Settler, PolygonMixin {
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
        } else {
            return false;
        }
        return true;
    }

    function _handlePermit(address owner, address token, Permit.PermitType permitType, bytes memory permitData) internal override {
        if (permitType == Permit.PermitType.ERC2612) {
            callPermit(owner, token, permitData);
        } else if (permitType == Permit.PermitType.DAIPermit) {
            callDAIPermit(owner, token, permitData);
        } else if (permitType == Permit.PermitType.NativeMetaTransaction) {
            callNativeMetaTransaction(owner, token, permitData);
        } else {
            Panic.panic(Panic.ENUM_CAST);
        }
    }

    // Solidity inheritance is stupid
    function _isRestrictedTarget(address target) internal view override(Settler, PolygonMixin) returns (bool) {
        return super._isRestrictedTarget(target);
    }

    function _dispatch(uint256 i, uint256 action, bytes calldata data)
        internal
        override(Settler, PolygonMixin)
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
        override(Permit2PaymentAbstract, PolygonMixin)
        returns (bool, bytes memory)
    {
        return super._fallback(data);
    }
}

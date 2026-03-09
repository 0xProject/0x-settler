// SPDX-License-Identifier: MIT
pragma solidity =0.8.33;

import {TempoMixin} from "./Common.sol";
import {SettlerMetaTxn} from "../../SettlerMetaTxn.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ISettlerActions} from "../../ISettlerActions.sol";

// Solidity inheritance is stupid
import {SettlerAbstract} from "../../SettlerAbstract.sol";
import {SettlerBase} from "../../SettlerBase.sol";
import {AbstractContext} from "../../Context.sol";
import {Permit2PaymentAbstract} from "../../core/Permit2PaymentAbstract.sol";
import {Permit2PaymentBase} from "../../core/Permit2Payment.sol";

/// @custom:security-contact security@0x.org
contract TempoSettlerMetaTxn is SettlerMetaTxn, TempoMixin {
    constructor(bytes20 gitCommit) SettlerBase(gitCommit) {}

    function _dispatchVIP(uint256 action, bytes calldata data, bytes calldata sig)
        internal
        virtual
        override
        DANGEROUS_freeMemory
        returns (bool)
    {
        // This does not make use of `super._dispatchVIP`. This chain's Settler is extremely
        // stripped-down and has almost no capabilities
        if (action == uint32(ISettlerActions.METATXN_TRANSFER_FROM.selector)) {
            (address recipient, ISignatureTransfer.PermitTransferFrom memory permit) =
                abi.decode(data, (address, ISignatureTransfer.PermitTransferFrom));
            (ISignatureTransfer.SignatureTransferDetails memory transferDetails,) =
                _permitToTransferDetails(permit, recipient);

            // We simultaneously transfer-in the taker's tokens and authenticate the
            // metatransaction.
            _transferFrom(permit, transferDetails, sig);
        } else {
            return false;
        }
        return true;
    }

    // Solidity inheritance is stupid
    function _dispatch(uint256 i, uint256 action, bytes calldata data)
        internal
        virtual
        override(SettlerAbstract, SettlerBase, TempoMixin)
        returns (bool)
    {
        return super._dispatch(i, action, data);
    }

    function _msgSender() internal view virtual override(SettlerMetaTxn, AbstractContext) returns (address) {
        return super._msgSender();
    }

    function _isRestrictedTarget(address target)
        internal
        view
        virtual
        override(SettlerMetaTxn, Permit2PaymentAbstract)
        returns (bool)
    {
        return super._isRestrictedTarget(target);
    }

    function _fallback(bytes calldata data)
        internal
        virtual
        override(Permit2PaymentAbstract, TempoMixin)
        returns (bool, bytes memory)
    {
        return super._fallback(data);
    }
}

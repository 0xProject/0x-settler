// SPDX-License-Identifier: MIT
pragma solidity =0.8.34;

import {HyperEvmCommon} from "./Common.sol";
import {SettlerMetaTxn} from "../../SettlerMetaTxn.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ISettlerActions} from "../../ISettlerActions.sol";

// Solidity inheritance is stupid
import {SettlerAbstract} from "../../SettlerAbstract.sol";
import {SettlerBase} from "../../SettlerBase.sol";
import {Permit2PaymentAbstract} from "../../core/Permit2PaymentAbstract.sol";
import {AbstractContext} from "../../Context.sol";
import {Permit2PaymentBase} from "../../core/Permit2Payment.sol";

/// @custom:security-contact security@0x.org
contract HyperEvmSettlerMetaTxn is SettlerMetaTxn, HyperEvmCommon {
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
        } else {
            return false;
        }
        return true;
    }

    // Solidity inheritance is stupid
    function _hasRecipientCheck()
        internal
        pure
        virtual
        override(SettlerAbstract, SettlerBase, HyperEvmCommon)
        returns (bool)
    {
        return super._hasRecipientCheck();
    }

    function _checkRecipient(address sender, address recipient, IERC20 buyToken)
        internal
        view
        virtual
        override(SettlerAbstract, SettlerBase, HyperEvmCommon)
    {
        super._checkRecipient(sender, recipient, buyToken);
    }

    function _dispatch(uint256 i, uint256 action, bytes calldata data, AllowedSlippage memory slippage)
        internal
        virtual
        override(SettlerBase, HyperEvmCommon)
        returns (bool)
    {
        return super._dispatch(i, action, data, slippage);
    }

    function _msgSender() internal view virtual override(SettlerMetaTxn, AbstractContext) returns (address) {
        return super._msgSender();
    }

    function _isRestrictedTarget(address target)
        internal
        view
        virtual
        override(SettlerMetaTxn, HyperEvmCommon)
        returns (bool)
    {
        return super._isRestrictedTarget(target);
    }

    function _fallback(bytes calldata data)
        internal
        virtual
        override(Permit2PaymentAbstract, HyperEvmCommon)
        returns (bool, bytes memory)
    {
        return super._fallback(data);
    }
}

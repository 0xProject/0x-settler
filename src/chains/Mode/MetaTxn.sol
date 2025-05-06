// SPDX-License-Identifier: MIT
pragma solidity =0.8.25;

import {ModeMixin} from "./Common.sol";
import {SettlerMetaTxn} from "../../SettlerMetaTxn.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ISettlerActions} from "../../ISettlerActions.sol";

// Solidity inheritance is stupid
import {SettlerAbstract} from "../../SettlerAbstract.sol";
import {SettlerBase} from "../../SettlerBase.sol";
import {AbstractContext} from "../../Context.sol";
import {PaymentAbstract} from "../../core/PaymentAbstract.sol";
import {Permit2PaymentBase} from "../../core/Permit2Payment.sol";

/// @custom:security-contact security@0x.org
contract ModeSettlerMetaTxn is SettlerMetaTxn, ModeMixin {
    constructor(bytes20 gitCommit) SettlerBase(gitCommit) {}

    function _dispatchVIP(uint256 action, bytes calldata data, bytes calldata sig)
        internal
        virtual
        override
        DANGEROUS_freeMemory
        returns (bool)
    {
        return super._dispatchVIP(action, data, sig);
    }

    function _isRestrictedTarget(address target)
        internal
        pure
        virtual
        override(Permit2PaymentBase, ModeMixin, PaymentAbstract)
        returns (bool)
    {
        return ModeMixin._isRestrictedTarget(target) || Permit2PaymentBase._isRestrictedTarget(target);
    }

    // Solidity inheritance is stupid
    function _dispatch(uint256 i, uint256 action, bytes calldata data)
        internal
        virtual
        override(SettlerAbstract, SettlerBase, ModeMixin)
        returns (bool)
    {
        return super._dispatch(i, action, data);
    }
}

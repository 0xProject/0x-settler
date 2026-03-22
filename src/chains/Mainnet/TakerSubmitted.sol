// SPDX-License-Identifier: MIT
pragma solidity =0.8.33;

import {MainnetMixin} from "./Common.sol";
import {Settler} from "../../Settler.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ISettlerActions} from "../../ISettlerActions.sol";

// Solidity inheritance is stupid
import {SettlerSwapAbstract} from "../../SettlerAbstract.sol";
import {SettlerBase} from "../../SettlerBase.sol";
import {Permit2PaymentAbstract} from "../../core/Permit2PaymentAbstract.sol";
import {AbstractContext} from "../../Context.sol";

/// @custom:security-contact security@0x.org
contract MainnetSettler is Settler, MainnetMixin {
    constructor(bytes20 gitCommit) SettlerBase(gitCommit) {}

    function _dispatch(uint256 i, uint256 action, bytes calldata data, AllowedSlippage memory slippage)
        internal
        override(Settler, MainnetMixin)
        returns (bool)
    {
        return super._dispatch(i, action, data, slippage);
    }

    function _dispatchVIP(uint256 action, bytes calldata data, AllowedSlippage memory slippage)
        internal
        override(Settler, MainnetMixin)
        DANGEROUS_freeMemory
        returns (bool)
    {
        return super._dispatchVIP(action, data, slippage);
    }

    // Solidity inheritance is stupid
    function _isRestrictedTarget(address target)
        internal
        view
        override(Settler, MainnetMixin)
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
        override(Permit2PaymentAbstract, MainnetMixin)
        returns (bool, bytes memory)
    {
        return super._fallback(data);
    }
}

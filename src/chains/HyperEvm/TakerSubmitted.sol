// SPDX-License-Identifier: MIT
pragma solidity =0.8.34;

import {HyperEvmMixin} from "./Common.sol";
import {Settler} from "../../Settler.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ISettlerActions} from "../../ISettlerActions.sol";

// Solidity inheritance is stupid
import {SettlerAbstract} from "../../SettlerAbstract.sol";
import {SettlerBase} from "../../SettlerBase.sol";
import {AbstractContext} from "../../Context.sol";

/// @custom:security-contact security@0x.org
contract HyperEvmSettler is Settler, HyperEvmMixin {
    constructor(bytes20 gitCommit) SettlerBase(gitCommit) {}

    function _dispatchVIP(uint256 action, bytes calldata data) internal override DANGEROUS_freeMemory returns (bool) {
        if (super._dispatchVIP(action, data)) {
            return true;
        } else {
            return false;
        }
        return true;
    }

    // Solidity inheritance is stupid
    function _hasRecipientCheck() internal pure override(SettlerAbstract, SettlerBase, HyperEvmMixin) returns (bool) {
        return super._hasRecipientCheck();
    }

    function _checkRecipient(address sender, address recipient, IERC20 buyToken)
        internal
        view
        override(SettlerAbstract, SettlerBase, HyperEvmMixin)
    {
        super._checkRecipient(sender, recipient, buyToken);
    }

    function _isRestrictedTarget(address target) internal view override(Settler, HyperEvmMixin) returns (bool) {
        return super._isRestrictedTarget(target);
    }

    function _dispatch(uint256 i, uint256 action, bytes calldata data, AllowedSlippage memory slippage)
        internal
        override(Settler, HyperEvmMixin)
        returns (bool)
    {
        return super._dispatch(i, action, data, slippage);
    }

    function _msgSender() internal view override(Settler, AbstractContext) returns (address) {
        return super._msgSender();
    }
}

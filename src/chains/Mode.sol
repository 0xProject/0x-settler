// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {SettlerBase} from "../SettlerBase.sol";
import {Settler} from "../Settler.sol";
import {SettlerMetaTxn} from "../SettlerMetaTxn.sol";

import {FreeMemory} from "../utils/FreeMemory.sol";

import {ISettlerActions} from "../ISettlerActions.sol";
import {UnknownForkId} from "../core/SettlerErrors.sol";

import {MODE_SFS} from "./IModeSFS.sol";

// Solidity inheritance is stupid
import {SettlerAbstract} from "../SettlerAbstract.sol";
import {AbstractContext} from "../Context.sol";
import {Permit2PaymentAbstract} from "../core/Permit2PaymentAbstract.sol";
import {Permit2PaymentBase} from "../core/Permit2Payment.sol";

abstract contract ModeMixin is FreeMemory, SettlerBase {
    constructor() {
        assert(block.chainid == 34443 || block.chainid == 31337);
        MODE_SFS.assign(MODE_SFS.getTokenId(0x00000000000004533Fe15556B1E086BB1A72cEae));
    }

    function _isRestrictedTarget(address target)
        internal
        pure
        virtual
        override(Permit2PaymentAbstract)
        returns (bool)
    {
        return target == address(MODE_SFS);
    }
    
    function _dispatch(uint256 i, bytes4 action, bytes calldata data)
        internal
        virtual
        override(SettlerBase)
        DANGEROUS_freeMemory
        returns (bool)
    {
        return super._dispatch(i, action, data);
    }

    function _uniV3ForkInfo(uint8 forkId)
        internal
        pure
        override
        returns (address, bytes32, uint32)
    {
        revert UnknownForkId(forkId);
    }
}

/// @custom:security-contact security@0x.org
contract ModeSettler is Settler, ModeMixin {
    constructor(bytes20 gitCommit) Settler(gitCommit) {}

    function _dispatchVIP(bytes4 action, bytes calldata data) internal override DANGEROUS_freeMemory returns (bool) {
        return super._dispatchVIP(action, data);
    }

    function _isRestrictedTarget(address target)
        internal
        pure
        override(Settler, ModeMixin)
        returns (bool)
    {
        return ModeMixin._isRestrictedTarget(target) || Settler._isRestrictedTarget(target);
    }

    // Solidity inheritance is stupid
    function _dispatch(uint256 i, bytes4 action, bytes calldata data)
        internal
        override(SettlerAbstract, SettlerBase, ModeMixin)
        returns (bool)
    {
        return super._dispatch(i, action, data);
    }

    function _msgSender() internal view override(Settler, AbstractContext) returns (address) {
        return super._msgSender();
    }
}

/// @custom:security-contact security@0x.org
contract ModeSettlerMetaTxn is SettlerMetaTxn, ModeMixin {
    constructor(bytes20 gitCommit) SettlerMetaTxn(gitCommit) {}

    function _dispatchVIP(bytes4 action, bytes calldata data, bytes calldata sig)
        internal
        override
        DANGEROUS_freeMemory
        returns (bool)
    {
        return super._dispatchVIP(action, data, sig);
    }

    function _isRestrictedTarget(address target)
        internal
        pure
        override(Permit2PaymentBase, ModeMixin, Permit2PaymentAbstract)
        returns (bool)
    {
        return ModeMixin._isRestrictedTarget(target) || Permit2PaymentBase._isRestrictedTarget(target);
    }
    
    // Solidity inheritance is stupid
    function _dispatch(uint256 i, bytes4 action, bytes calldata data)
        internal
        override(SettlerAbstract, SettlerBase, ModeMixin)
        returns (bool)
    {
        return super._dispatch(i, action, data);
    }

    function _msgSender() internal view override(SettlerMetaTxn, AbstractContext) returns (address) {
        return super._msgSender();
    }
}

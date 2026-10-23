// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {Permit2PaymentAbstract} from "../../core/Permit2PaymentAbstract.sol";
import {SettlerAbstract} from "../../SettlerAbstract.sol";

import {FastLogic} from "../../utils/FastLogic.sol";

import {HyperCoreSystemAddress} from "../../core/SettlerErrors.sol";

abstract contract BlockHyperEvmSystemContracts is SettlerAbstract {
    using FastLogic for bool;

    // Queues an action on HyperCore for the account of `msg.sender`. One of those actions
    // registers an API wallet with lasting signing authority over that account.
    address internal constant _HYPEREVM_CORE_WRITER = 0x3333333333333333333333333333333333333333;
    // Native value sent here is credited on HyperCore to the account that sent it.
    address internal constant _HYPERCORE_HYPE_SYSTEM_ADDRESS = 0x2222222222222222222222222222222222222222;
    // Tokens sent to `0x2000...0000` plus the token's index are credited on HyperCore to the
    // account that sent them. The index occupies the low 8 bytes of the address.
    uint160 internal constant _HYPERCORE_TOKEN_SYSTEM_ADDRESS_PREFIX = 0x200000000000000000000000;

    function _isRestrictedTarget(address target) internal view virtual override(Permit2PaymentAbstract) returns (bool) {
        return super._isRestrictedTarget(target).or(target == _HYPEREVM_CORE_WRITER);
    }

    function _hasRecipientCheck() internal pure virtual override(SettlerAbstract) returns (bool) {
        return true;
    }

    // A transfer to a system address is credited on HyperCore to the account that funded it, not
    // to the address named as the recipient. Only a transfer funded by the payer reaches the
    // payer's HyperCore account. A transfer funded by this contract, a pool, or a maker would be
    // credited to that party, and the recipient would receive nothing.
    function _checkRecipient(address sender, address recipient, IERC20)
        internal
        view
        virtual
        override(SettlerAbstract)
    {
        // `&&` keeps the transient load of the payer off the path taken by ordinary recipients.
        if (
            (recipient == _HYPERCORE_HYPE_SYSTEM_ADDRESS)
                .or(uint160(recipient) >> 64 == _HYPERCORE_TOKEN_SYSTEM_ADDRESS_PREFIX) && sender != _msgSender()
        ) {
            revert HyperCoreSystemAddress(recipient);
        }
    }
}

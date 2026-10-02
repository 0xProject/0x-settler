// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {Permit2PaymentAbstract} from "../../core/Permit2PaymentAbstract.sol";
import {SettlerAbstract} from "../../SettlerAbstract.sol";

import {FastLogic} from "../../utils/FastLogic.sol";

import {ReceivePolicyBlocked} from "../../core/SettlerErrors.sol";

interface ITempoAddressRegistry {
    function resolveRecipient(address to) external view returns (address);
}

interface ITempoReceivePolicy {
    function validateReceivePolicy(address token, address sender, address receiver)
        external
        view
        returns (bool authorized, uint8 blockedReason);
}

abstract contract BlockTempoSystemContracts is SettlerAbstract {
    using FastLogic for bool;

    address internal constant _TEMPO_TIP403_REGISTRY = 0x403c000000000000000000000000000000000000;
    address internal constant _TEMPO_RECEIVE_POLICY_GUARD = 0xB10C000000000000000000000000000000000000;
    address internal constant _TEMPO_ADDRESS_REGISTRY = 0xfDC0000000000000000000000000000000000000;

    function _isRestrictedTarget(address target) internal view virtual override(Permit2PaymentAbstract) returns (bool) {
        return super._isRestrictedTarget(target).or(target == _TEMPO_TIP403_REGISTRY)
            .or(target == _TEMPO_RECEIVE_POLICY_GUARD);
    }

    function _hasRecipientCheck() internal pure virtual override(SettlerAbstract) returns (bool) {
        return true;
    }

    // A recipient's TIP-1028 receive policy can send a TIP-20 payout to the ReceivePolicyGuard
    // rather than the recipient. The payout must reach the recipient.
    function _checkRecipient(address recipient, IERC20 buyToken)
        internal
        view
        virtual
        override(SettlerAbstract)
    {
        if ((uint160(address(buyToken)) >> 64 == 0x20c000000000000000000000).andNot(recipient == address(this))) {
            address resolved = ITempoAddressRegistry(_TEMPO_ADDRESS_REGISTRY).resolveRecipient(recipient);
            (bool authorized,) = ITempoReceivePolicy(_TEMPO_TIP403_REGISTRY)
                .validateReceivePolicy(address(buyToken), address(this), resolved);
            if (!authorized) revert ReceivePolicyBlocked(recipient);
        }
    }
}

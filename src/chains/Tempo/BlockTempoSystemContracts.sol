// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Permit2PaymentAbstract} from "../../core/Permit2PaymentAbstract.sol";

import {FastLogic} from "../../utils/FastLogic.sol";

abstract contract BlockTempoSystemContracts is Permit2PaymentAbstract {
    using FastLogic for bool;

    address internal constant _TEMPO_TIP403_REGISTRY = 0x403c000000000000000000000000000000000000;
    address internal constant _TEMPO_RECEIVE_POLICY_GUARD = 0xB10C000000000000000000000000000000000000;

    function _isRestrictedTarget(address target) internal view virtual override returns (bool) {
        return super._isRestrictedTarget(target).or(target == _TEMPO_TIP403_REGISTRY)
            .or(target == _TEMPO_RECEIVE_POLICY_GUARD);
    }
}

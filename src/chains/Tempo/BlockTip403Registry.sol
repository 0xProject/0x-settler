// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Permit2PaymentAbstract} from "../../core/Permit2PaymentAbstract.sol";

import {FastLogic} from "../../utils/FastLogic.sol";

abstract contract BlockTip403Registry is Permit2PaymentAbstract {
    using FastLogic for bool;

    address internal constant tip403Registry = 0x403c000000000000000000000000000000000000;

    function _isRestrictedTarget(address target) internal view virtual override returns (bool) {
        return super._isRestrictedTarget(target).or(target == tip403Registry);
    }
}

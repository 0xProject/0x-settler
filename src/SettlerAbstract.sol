// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {Permit2PaymentAbstract} from "./core/Permit2Payment.sol";

abstract contract SettlerAbstract is Permit2PaymentAbstract {
    // Permit2 Witness for meta transactions
    string internal constant ACTIONS_AND_SLIPPAGE_TYPE =
        "ActionsAndSlippage(address buyToken,address recipient,uint256 minAmountOut,bytes[] actions)";
    // `string.concat` isn't recognized by solc as compile-time constant, but `abi.encodePacked` is
    string internal constant ACTIONS_AND_SLIPPAGE_WITNESS = string(
        abi.encodePacked("ActionsAndSlippage actionsAndSlippage)", ACTIONS_AND_SLIPPAGE_TYPE, TOKEN_PERMISSIONS_TYPE)
    );
    bytes32 internal constant ACTIONS_AND_SLIPPAGE_TYPEHASH =
        0x7d6b6ac05bf0d3f905c044bcb7baf6b20670f84c2275870747ac3b8fa8c43e12;

    constructor() {
        assert(ACTIONS_AND_SLIPPAGE_TYPEHASH == keccak256(bytes(ACTIONS_AND_SLIPPAGE_TYPE)));
    }
}

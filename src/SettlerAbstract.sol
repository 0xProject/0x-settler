// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Permit2PaymentAbstract} from "./core/Permit2PaymentAbstract.sol";

abstract contract SettlerAbstract is Permit2PaymentAbstract {
    // Permit2 Witness for meta transactions
    string internal constant ACTIONS_AND_SLIPPAGE_TYPE =
        "ActionsAndSlippage(address buyToken,address recipient,uint256 minAmountOut,bytes[] actions)";
    bytes32 internal constant ACTIONS_AND_SLIPPAGE_TYPEHASH =
        0x7d6b6ac05bf0d3f905c044bcb7baf6b20670f84c2275870747ac3b8fa8c43e12;

    constructor() {
        assert(ACTIONS_AND_SLIPPAGE_TYPEHASH == keccak256(bytes(ACTIONS_AND_SLIPPAGE_TYPE)));
    }

    function _hasMetaTxn() internal pure virtual returns (bool);

    function _dispatch(uint256 i, bytes4 action, bytes calldata data) internal virtual returns (bool);
}

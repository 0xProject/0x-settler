// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Permit2PaymentAbstract} from "./core/Permit2PaymentAbstract.sol";

abstract contract SettlerAbstract is Permit2PaymentAbstract {
    // Permit2 Witness for meta transactions
    string internal constant SLIPPAGE_AND_ACTIONS_TYPE =
        "SlippageAndActions(address recipient,address buyToken,uint256 minAmountOut,bytes[] actions)";
    bytes32 internal constant SLIPPAGE_AND_ACTIONS_TYPEHASH =
        0x615e8d716cef7295e75dd3f1f10d679914ad6d7759e8e9459f0109ef75241701;
    uint256 internal constant BASIS = 10_000;

    constructor() {
        assert(SLIPPAGE_AND_ACTIONS_TYPEHASH == keccak256(bytes(SLIPPAGE_AND_ACTIONS_TYPE)));
    }

    function _hasMetaTxn() internal pure virtual returns (bool);

    function _dispatch(uint256 i, bytes4 action, bytes calldata data) internal virtual returns (bool);
}

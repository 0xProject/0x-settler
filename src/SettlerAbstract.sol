// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {Permit2PaymentAbstract} from "./core/Permit2PaymentAbstract.sol";
import {uint512} from "./utils/512Math.sol";

/// @title SettlerAbstract
/// @notice Abstract contract defining core types and constants for Settler
abstract contract SettlerAbstract is Permit2PaymentAbstract {
    // Permit2 Witness for meta transactions
    string internal constant SLIPPAGE_AND_ACTIONS_TYPE =
        "SlippageAndActions(address recipient,address buyToken,uint256 minAmountOut,bytes[] actions)";
    bytes32 internal constant SLIPPAGE_AND_ACTIONS_TYPEHASH =
        0x615e8d716cef7295e75dd3f1f10d679914ad6d7759e8e9459f0109ef75241701;
    // Permit2 Witness for intents
    string internal constant SLIPPAGE_TYPE = "Slippage(address recipient,address buyToken,uint256 minAmountOut)";
    bytes32 internal constant SLIPPAGE_TYPEHASH = 0xdc83993a2ffc65b01b71ed08790b6e39c5c55d76937b62a3b5085b02071f1259;

    uint256 internal constant BASIS = 10_000;
    IERC20 internal constant ETH_ADDRESS = IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE);

    constructor() {
        assert(SLIPPAGE_AND_ACTIONS_TYPEHASH == keccak256(bytes(SLIPPAGE_AND_ACTIONS_TYPE)));
        assert(SLIPPAGE_TYPEHASH == keccak256(bytes(SLIPPAGE_TYPE)));
    }

    function _hasMetaTxn() internal pure virtual returns (bool);

    function _tokenId() internal pure virtual returns (uint256);

    function _dispatch(uint256 i, uint256 action, bytes calldata data) internal virtual returns (bool);

    function _div512to256(uint512 n, uint512 d) internal view virtual returns (uint256);
}

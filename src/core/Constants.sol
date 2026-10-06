// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";

// The denominator for all balance-proportional action arguments (parts-per-million).
uint256 constant BASIS = 1_000_000;

// ERC-7528 native asset designator.
address constant ETH_ADDRESS = 0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE;

function isNative(address token) pure returns (bool r) {
    assembly ("memory-safe") {
        r := iszero(shl(0x60, xor(ETH_ADDRESS, token)))
    }
}

function isNative(IERC20 token) pure returns (bool) {
    return isNative(address(token));
}

function compatBalance(IERC20 token, address holder) view returns (uint256) {
    return isNative(token) ? holder.balance : SafeTransferLib.fastBalanceOf(token, holder);
}

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

address constant zebraV3Factory = 0x96a7F53f7636c93735bf85dE416A4Ace94B56Bd9;
bytes32 constant zebraV3InitHash = 0xcf0b3414328c2bd327a4f093539d0d7d82fb94f893a2965c75cb470289cb5ac7;
uint8 constant zebraV3ForkId = 12;

interface IZebraV3SwapCallback {
    function zebraV3SwapCallback(int256 amount0Delta, int256 amount1Delta, bytes calldata data) external;
}

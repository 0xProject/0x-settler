// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

address constant pancakeSwapV3Factory = 0x41ff9AA7e16B8B1a8a8dc4f0eFacd93D02d071c9;
bytes32 constant pancakeSwapV3InitHash = 0x6ce8eb472fa82df5469c6ab6d485f17c3ad13c8cd7af59b3d4a8026c5ce0f7e2;
uint8 constant pancakeSwapV3ForkId = 1;

interface IPancakeSwapV3Callback {
    function pancakeV3SwapCallback(int256 amount0Delta, int256 amount1Delta, bytes calldata data) external;
}

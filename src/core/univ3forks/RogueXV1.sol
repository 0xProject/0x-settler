// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

address constant rogueXV1Factory = 0xF22FF8f7f430a2d07efB88015853D52C88BC286d;
bytes32 constant rogueXV1InitHash = 0x7eb89ab17cc883d055f470bc0250135af3f951b6403ea74f651bcba0136f210b;
uint8 constant rogueXV1ForkId = 20;

interface IRoxSpotSwapCallback {
    function swapCallback(int256 amount0Delta, int256 amount1Delta, bytes calldata data) external;
}

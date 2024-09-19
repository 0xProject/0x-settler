// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

address constant blasterV3Factory = 0x1A8027625C830aAC43aD82a3f7cD6D5fdCE89d78;
bytes32 constant blasterV3InitHash = 0x708ef7fcba73b894862b667ec8c8ea3bef8c3f2a022dc8314152dfb52b4a1b67;
uint8 constant blasterV3ForkId = 18;

interface IBlasterswapV3SwapCallback {
    function blasterswapV3SwapCallback(int256 amount0Delta, int256 amount1Delta, bytes calldata data) external;
}

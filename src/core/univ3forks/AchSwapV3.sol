// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

address constant achSwapV3Factory = 0xaE54BF4C8078BaAAf7e17f8e01659Ea470a989FC;
bytes32 constant achSwapV3InitHash = 0x86a79abdb3735ffdb1ded2e8eb23e704e9d72d535c11d5462cafaa7cb269cc85;
uint8 constant achSwapV3ForkId = 47;

interface IAchSwapV3SwapCallback {
    function AchSwapV3SwapCallback(int256 amount0Delta, int256 amount1Delta, bytes calldata data) external;
}

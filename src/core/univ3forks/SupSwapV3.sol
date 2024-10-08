// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

address constant supSwapV3Factory = 0xDd0B32Bc487AE1487B0F4e5C8c44FC9d30A25dD7;
bytes32 constant supSwapV3InitHash = 0x3e03ddab0aa29c12c46cd283f9cf8c6800eb7ea3c6530a382474bac82333f2e0;
uint8 constant supSwapV3ForkId = 21;

interface ISupSwapV3Callback {
    function supV3SwapCallback(int256 amount0Delta, int256 amount1Delta, bytes calldata data) external;
}

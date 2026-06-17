// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

address constant squadSwapV3PoolDeployer = 0x127AA917Ace4a3880fa5E193947F2190829144A4;
bytes32 constant squadSwapV3InitHash = 0xff132c7c84e5449c9d69fc8490aba7f25fe4033e8889a13556c416128e1308cf;
uint8 constant squadSwapV3ForkId = 38;

interface ISquadSwapV3Callback {
    function squadV3SwapCallback(int256 amount0Delta, int256 amount1Delta, bytes calldata data) external;
}

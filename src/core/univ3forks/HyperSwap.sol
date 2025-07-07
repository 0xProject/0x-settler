// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

address constant hyperSwapFactory = 0xB1c0fa0B789320044A6F623cFe5eBda9562602E3;
bytes32 constant hyperSwapInitHash = 0xe3572921be1688dba92df30c6781b8770499ff274d20ae9b325f4242634774fb;
uint8 constant hyperSwapForkId = 34;

interface IHyperswapV3SwapCallback {
    function hyperswapV3SwapCallback(int256 amount0Delta, int256 amount1Delta, bytes calldata data) external;
}

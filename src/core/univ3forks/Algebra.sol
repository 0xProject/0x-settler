// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

bytes32 constant algebraV4InitHash = 0xf96d2474815c32e070cd63233f06af5413efc5dcb430aee4ff18cc29007c562d;

interface IAlgebraCallback {
    function algebraSwapCallback(int256 amount0Delta, int256 amount1Delta, bytes calldata data) external;
}

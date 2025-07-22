// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

interface IMultiCall {
    function multicall(bytes[] calldata datas) external;
}

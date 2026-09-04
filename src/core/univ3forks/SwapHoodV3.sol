// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

// SwapHood V3 is a PancakeSwap V3 fork on RobinHood. `swapHoodV3Factory` is the
// PoolDeployer (the CREATE2 deployer of the pools), not the pool factory. SwapHood
// V3 shares the PancakeSwap V3 callback (`pancakeV3SwapCallback`).
address constant swapHoodV3Factory = 0xcB42A120795Ca98F762fdcCf43Cc4aB6D62bF1B2;
bytes32 constant swapHoodV3InitHash = 0x9fca60359d787088d07f1c02f8be93ad13a3d45923e6d60b9032f18b5ac973aa;
uint8 constant swapHoodV3ForkId = 42;

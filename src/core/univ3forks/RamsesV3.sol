// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

// Ramses V3 (concentrated liquidity) is a UniswapV3 fork on RobinHood.
// `ramsesV3Factory` is the RamsesV3PoolDeployer (the CREATE2 deployer of the
// pools), not the pool factory. Pools are keyed by `tickSpacing` (the off-chain
// router encodes `tickSpacing` as the `uint24` poolId). `ramsesV3InitHash` is the
// hash of Ramses' constant 55-byte bootstrap-stub init code, not the pool
// bytecode. Ramses V3 uses the standard UniswapV3 callback (`uniswapV3SwapCallback`).
address constant ramsesV3Factory = 0x4b37359BF291AbE8453692DB58d515a8b013Dca9;
bytes32 constant ramsesV3InitHash = 0x892f127ed4b26ca352056c8fb54585a3268f76f97fdd84d5836ef4bda8d8c685;
uint8 constant ramsesV3ForkId = 46;

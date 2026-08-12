// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

// RobinSwap V3 is a Uniswap V3 fork on RobinHood; `robinSwapV3Factory` is the
// CREATE2 pool deployer. Its pools share the same init code hash as PrjxV3, so the
// init hash is imported from PrjxV3 rather than redeclared (see RobinHood Common.sol).
address constant robinSwapV3Factory = 0xEa561E058313B96011e5070Ca7d0f027A44E3748;
uint8 constant robinSwapV3ForkId = 43;

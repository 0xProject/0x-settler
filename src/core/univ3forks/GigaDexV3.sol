// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

// GigaDEX (concentrated liquidity, "CLPool") is a PancakeSwap V3 fork on RobinHood.
// `gigaDexV3Factory` is the PoolDeployer (the CREATE2 deployer of the pools), not the
// pool factory. GigaDEX V3 shares the PancakeSwap V3 callback (`pancakeV3SwapCallback`).
address constant gigaDexV3Factory = 0x5952F5D501a130da00fa8fE2257d8B35ddc0A57B;
bytes32 constant gigaDexV3InitHash = 0xfd3b64c598013443d9bb6db0da30281063a1a31138e23b55395d600154969b68;
uint8 constant gigaDexV3ForkId = 45;

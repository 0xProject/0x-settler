// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

// QuickSwapV4 is an Algebra Integral (v1.2.2) DEX on Polygon. `quickSwapV4Factory` is the
// Algebra pool deployer (the CREATE2 deployer of the pools), not the pool factory.
address constant quickSwapV4Factory = 0x96B31b1d17dee49e70B950dE33FFF83728f5c181;
bytes32 constant quickSwapV4InitHash = 0x62441ebe4e4315cf3d49d5957f94d66b253dbabe7006f34ad7f70947e60bf15c;
uint8 constant quickSwapV4ForkId = 44;

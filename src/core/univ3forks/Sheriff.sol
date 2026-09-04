// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

// Sheriff is an Algebra Integral (v1.2.2) DEX on RobinHood. `sheriffFactory` is the
// Algebra pool deployer (the CREATE2 deployer of the pools), not the pool factory.
address constant sheriffFactory = 0x9ac30D72168a4498aE5C80226F4d3C86278e8f80;
bytes32 constant sheriffInitHash = 0x62441ebe4e4315cf3d49d5957f94d66b253dbabe7006f34ad7f70947e60bf15c;
uint8 constant sheriffForkId = 41;

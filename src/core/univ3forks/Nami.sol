// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

// Algebra pools use the pool deployer, rather than the factory, for CREATE2 derivation.
address constant namiMainnetFactory = 0x86641A77A1172c3CE65bCE52aE91BDADEf0f74c2;
address constant namiBaseFactory = 0x79Ea2E90590089bbD13A0C6B5593D71C9E6f78ad;
address constant namiRobinhoodFactory = 0xC75fbF81cc29d71589bE9D3c70E6a4eDC41Ac6BC;
bytes32 constant namiInitHash = 0x62441ebe4e4315cf3d49d5957f94d66b253dbabe7006f34ad7f70947e60bf15c;
uint8 constant namiForkId = 49;

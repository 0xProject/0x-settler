// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IPoolManager} from "../UniswapV4Types.sol";

IPoolManager constant uniswapV4MainnetPoolManager = IPoolManager(0x000000000004444c5dc75cB358380D2e3dE08A90);
IPoolManager constant uniswapV4ArbitrumPoolManager = IPoolManager(0x360E68faCcca8cA495c1B759Fd9EEe466db9FB32);
IPoolManager constant uniswapV4AvalanchePoolManager = IPoolManager(0x06380C0e0912312B5150364B9DC4542BA0DbBc85);
IPoolManager constant uniswapV4BasePoolManager = IPoolManager(0x498581fF718922c3f8e6A244956aF099B2652b2b);
IPoolManager constant uniswapV4BnbPoolManager = IPoolManager(0x28e2Ea090877bF75740558f6BFB36A5ffeE9e9dF);
IPoolManager constant uniswapV4OptimismPoolManager = IPoolManager(0x9a13F98Cb987694C9F086b1F5eB990EeA8264Ec3);
IPoolManager constant uniswapV4PolygonPoolManager = IPoolManager(0x67366782805870060151383F4BbFF9daB53e5cD6);
IPoolManager constant uniswapV4WorldChainPoolManager = IPoolManager(0xb1860D529182ac3BC1F51Fa2ABd56662b7D13f33);
IPoolManager constant uniswapV4InkPoolManager = IPoolManager(0x360E68faCcca8cA495c1B759Fd9EEe466db9FB32);
IPoolManager constant uniswapV4UnichainPoolManager = IPoolManager(0x1F98400000000000000000000000000000000004); // https://github.com/Uniswap/contracts/blob/main/deployments/130.md#wed-jan-22-2025
IPoolManager constant uniswapV4SepoliaPoolManager = IPoolManager(0xE03A1074c86CFeDd5C142C4F04F1a1536e203543);
IPoolManager constant uniswapV4MonadPoolManager = IPoolManager(0x188d586Ddcf52439676Ca21A244753fA19F9Ea8e);
IPoolManager constant uniswapV4TempoPoolManager = IPoolManager(0x33620f62C5b9B2086dD6b62F4A297A9f30347029);
IPoolManager constant uniswapV4RobinhoodPoolManager = IPoolManager(0x8366a39CC670B4001A1121B8F6A443A643e40951);
IPoolManager constant uniswapV4ArcPoolManager = IPoolManager(0x8366a39CC670B4001A1121B8F6A443A643e40951);

uint8 constant uniswapV4ForkId = 0;

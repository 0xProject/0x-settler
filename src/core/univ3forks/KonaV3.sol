// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

// Kona V3 is a Uniswap V3 fork (PunchSwap V3 lineage) on Abstract. `konaV3Factory` is also
// the CREATE2 deployer of the pools. `konaV3InitHash` is the EraVM versioned bytecode hash
// of the pool, not the hash of its creation code. The swap callback is renamed from
// `uniswapV3SwapCallback` to `punchSwapV3SwapCallback`.
address constant konaV3Factory = 0xfeD3612D6865ca46F080f19fc34AA8Cac0C92cF6;
bytes32 constant konaV3InitHash = 0x01001099bcaa98e0dc95de15514cebfb0d7778a993f8d2107ed1d5d8e7860ac2;
uint8 constant konaV3ForkId = 47;

interface IPunchSwapV3Callback {
    function punchSwapV3SwapCallback(int256 amount0Delta, int256 amount1Delta, bytes calldata data) external;
}

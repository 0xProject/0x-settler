// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

address constant uniswapV3MainnetFactory = 0x1F98431c8aD98523631AE4a59f267346ea31F984;
address constant uniswapV3SepoliaFactory = 0x0227628f3F023bb0B980b67D528571c95c6DaC1c;
address constant uniswapV3BaseFactory = 0x33128a8fC17869897dcE68Ed026d694621f6FDfD;
address constant uniswapV3BnbFactory = 0xdB1d10011AD0Ff90774D0C6Bb92e5C5c8b4461F7;
address constant uniswapV3AvalancheFactory = 0x740b1c1de25031C31FF4fC9A62f554A55cdC1baD;
address constant uniswapV3BlastFactory = 0x792edAdE80af5fC680d96a2eD80A44247D2Cf6Fd;
address constant uniswapV3ScrollFactory = 0x70C62C8b8e801124A4Aa81ce07b637A3e83cb919;
address constant uniswapV3LineaFactory = 0x31FAfd4889FA1269F7a13A66eE0fB458f27D72A9;
address constant uniswapV3MantleFactory = 0x0d922Fb1Bc191F64970ac40376643808b4B74Df9;
address constant uniswapV3TaikoFactory = 0x75FC67473A91335B5b8F8821277262a13B38c9b3;
address constant uniswapV3WorldChainFactory = 0x7a5028BDa40e7B173C278C5342087826455ea25a;
address constant uniswapV3GnosisFactory = 0xe32F7dD7e3f098D518ff19A22d5f028e076489B1;
address constant uniswapV3SonicFactory = 0xcb2436774C3e191c85056d248EF4260ce5f27A9D;
address constant uniswapV3InkFactory = 0x640887A9ba3A9C53Ed27D0F7e8246A4F933f3424;
address constant uniswapV3MonadTestnetFactory = 0x961235a9020B05C44DF1026D956D1F4D78014276;
address constant uniswapV3UnichainFactory = 0x0000000000000000000000000000000000000000; // TODO: likely 0x1F98431c8aD98523631AE4a59f267346ea31F984, in which case remove this line and replace references with `uniswapV3MainnetFactory`
bytes32 constant uniswapV3InitHash = 0xe34f199b19b2b4f47f68442619d555527d244f78a3297ea89325f843f87b8b54;
uint8 constant uniswapV3ForkId = 0;

interface IUniswapV3Callback {
    function uniswapV3SwapCallback(int256 amount0Delta, int256 amount1Delta, bytes calldata data) external;
}

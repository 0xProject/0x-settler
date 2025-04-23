// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {UniswapV2PairTest} from "./UniswapV2PairTest.t.sol";
import {UniswapV3PairTest} from "./UniswapV3PairTest.t.sol";
import {UniswapV4PairTest} from "./UniswapV4PairTest.t.sol";

import {ICurveV2Pool} from "./vendor/ICurveV2Pool.sol";
import {SettlerBasePairTest} from "./SettlerBasePairTest.t.sol";
import {SettlerPairTest} from "./SettlerPairTest.t.sol";
import {MainnetDefaultFork} from "./BaseForkTest.t.sol";

contract WETHUSDCTest is UniswapV2PairTest, UniswapV3PairTest, UniswapV4PairTest {
    function setUp() public override(SettlerBasePairTest, SettlerPairTest, UniswapV3PairTest) {
        super.setUp();
    }

    function testName() internal pure override returns (string memory) {
        return "WETH-USDC";
    }

    function fromToken() internal pure override returns (IERC20) {
        return IERC20(0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2);
    }

    function toToken() internal pure override returns (IERC20) {
        return IERC20(0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48);
    }

    function amount() internal pure override returns (uint256) {
        return 1 ether;
    }

    function uniswapV3Path() internal pure override(SettlerPairTest) returns (bytes memory) {
        return abi.encodePacked(fromToken(), uint8(0), uint24(500), toToken());
    }

    function uniswapV3PathCompat() internal pure override(UniswapV3PairTest) returns (bytes memory) {
        return abi.encodePacked(fromToken(), uint24(500), toToken());
    }

    function uniswapV2Pool() internal pure override(SettlerPairTest) returns (address) {
        return 0xB4e16d0168e52d35CaCD2c6185b44281Ec28C9Dc;
    }

    function getCurveV2PoolData()
        internal
        pure
        override(SettlerPairTest)
        returns (ICurveV2Pool.CurveV2PoolData memory poolData)
    {}

    function testBlockNumber()
        internal
        pure
        virtual
        override(MainnetDefaultFork, UniswapV3PairTest)
        returns (uint256)
    {
        return super.testBlockNumber();
    }
}

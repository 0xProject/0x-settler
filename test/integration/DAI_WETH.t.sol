// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {AllowanceHolderPairTest} from "./AllowanceHolderPairTest.t.sol";
import {ZeroExPairTest} from "./ZeroExPairTest.t.sol";
import {UniswapV2PairTest} from "./UniswapV2PairTest.t.sol";
import {UniswapV3PairTest} from "./UniswapV3PairTest.t.sol";
import {UniswapV4PairTest} from "./UniswapV4PairTest.t.sol";
import {SettlerPairTest} from "./SettlerPairTest.t.sol";
import {SettlerMetaTxnPairTest} from "./SettlerMetaTxnPairTest.t.sol";
import {TokenTransferTest} from "./TokenTransferTest.t.sol";

import {SettlerBasePairTest} from "./SettlerBasePairTest.t.sol";
import {ICurveV2Pool} from "./vendor/ICurveV2Pool.sol";
import {MainnetDefaultFork} from "./BaseForkTest.t.sol";

contract DAIWETHTest is
    AllowanceHolderPairTest,
    SettlerPairTest,
    SettlerMetaTxnPairTest,
    TokenTransferTest,
    UniswapV2PairTest,
    UniswapV3PairTest,
    UniswapV4PairTest,
    ZeroExPairTest
{
    function setUp()
        public
        override(
            SettlerBasePairTest,
            AllowanceHolderPairTest,
            SettlerPairTest,
            SettlerMetaTxnPairTest,
            TokenTransferTest,
            UniswapV3PairTest,
            ZeroExPairTest
        )
    {
        super.setUp();
    }

    function _testName() internal pure override returns (string memory) {
        return "DAI-WETH";
    }

    function fromToken() internal pure override returns (IERC20) {
        return IERC20(0x6B175474E89094C44Da98b954EedeAC495271d0F);
    }

    function toToken() internal pure override returns (IERC20) {
        return IERC20(0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2);
    }

    function amount() internal pure override returns (uint256) {
        return 1000e18;
    }

    function slippageLimit() internal pure override returns (uint256) {
        return 0.5 ether;
    }

    function _testBlockNumber()
        internal
        pure
        virtual
        override(MainnetDefaultFork, UniswapV3PairTest)
        returns (uint256)
    {
        return super._testBlockNumber();
    }

    function uniswapV3Path()
        internal
        view
        override(SettlerPairTest, AllowanceHolderPairTest, SettlerMetaTxnPairTest)
        returns (bytes memory)
    {
        return abi.encodePacked(fromToken(), uint8(0), uint24(3000), sqrtPriceLimitX96FromTo(), toToken());
    }

    function uniswapV3PathCompat() internal pure override(UniswapV3PairTest, ZeroExPairTest) returns (bytes memory) {
        return abi.encodePacked(fromToken(), uint24(3000), toToken());
    }

    function uniswapV2Pool() internal pure override(SettlerPairTest, AllowanceHolderPairTest) returns (address) {
        return 0xA478c2975Ab1Ea89e8196811F51A7B7Ade33eB11;
    }

    function uniswapV4FeeTier() internal view virtual override returns (uint24) {
        return 3000;
    }

    function uniswapV4TickSpacing() internal view virtual override returns (int24) {
        return 60;
    }

    function getCurveV2PoolData()
        internal
        pure
        override(SettlerPairTest, ZeroExPairTest)
        returns (ICurveV2Pool.CurveV2PoolData memory poolData)
    {}
}

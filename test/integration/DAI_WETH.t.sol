// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "forge-std/interfaces/IERC20.sol";

import {AllowanceHolderPairTest} from "./AllowanceHolderPairTest.t.sol";
import {ZeroExPairTest} from "./ZeroExPairTest.t.sol";
import {UniswapV3PairTest} from "./UniswapV3PairTest.t.sol";
import {SettlerPairTest} from "./SettlerPairTest.t.sol";
import {SettlerMetaTxnPairTest} from "./SettlerMetaTxnPairTest.t.sol";
import {TokenTransferTest} from "./TokenTransferTest.t.sol";

import {ICurveV2Pool} from "./vendor/ICurveV2Pool.sol";

contract DAIWETHTest is
    AllowanceHolderPairTest,
    SettlerPairTest,
    SettlerMetaTxnPairTest,
    TokenTransferTest,
    UniswapV3PairTest,
    ZeroExPairTest
{
    function setUp()
        public
        override(
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

    function testName() internal pure override returns (string memory) {
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

    function uniswapV3Path()
        internal
        pure
        override(SettlerPairTest, AllowanceHolderPairTest, SettlerMetaTxnPairTest)
        returns (bytes memory)
    {
        return abi.encodePacked(fromToken(), uint8(0), uint24(500), toToken());
    }

    function uniswapV3PathCompat() internal pure override(UniswapV3PairTest, ZeroExPairTest) returns (bytes memory) {
        return abi.encodePacked(fromToken(), uint24(500), toToken());
    }

    function uniswapV2Pool() internal pure override(SettlerPairTest, AllowanceHolderPairTest) returns (address) {
        return 0xC3D03e4F041Fd4cD388c549Ee2A29a9E5075882f; // Sushiswap DAI/WETH
    }

    function getCurveV2PoolData()
        internal
        pure
        override(SettlerPairTest, ZeroExPairTest)
        returns (ICurveV2Pool.CurveV2PoolData memory poolData)
    {}
}

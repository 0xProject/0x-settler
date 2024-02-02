// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {IERC20} from "../../src/IERC20.sol";

import {AllowanceHolderPairTest} from "./AllowanceHolderPairTest.t.sol";
import {SettlerPairTest} from "./SettlerPairTest.t.sol";
import {SettlerMetaTxnPairTest} from "./SettlerMetaTxnPairTest.t.sol";
import {UniswapV3PairTest} from "./UniswapV3PairTest.t.sol";
import {ZeroExPairTest} from "./ZeroExPairTest.t.sol";
import {TokenTransferTest} from "./TokenTransferTest.t.sol";
import {CurveV2PairTest} from "./CurveV2PairTest.t.sol";
import {ICurveV2Pool} from "./vendor/ICurveV2Pool.sol";

contract USDTWETHTest is
    AllowanceHolderPairTest,
    CurveV2PairTest,
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
            CurveV2PairTest,
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
        return "USDT-WETH";
    }

    function fromToken() internal pure override returns (IERC20) {
        return IERC20(0xdAC17F958D2ee523a2206206994597C13D831ec7);
    }

    function toToken() internal pure override returns (IERC20) {
        return IERC20(0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2);
    }

    function amount() internal pure override returns (uint256) {
        return 1000e6;
    }

    function getCurveV2PoolData()
        internal
        pure
        override(CurveV2PairTest, SettlerPairTest, ZeroExPairTest)
        returns (ICurveV2Pool.CurveV2PoolData memory poolData)
    {
        poolData = ICurveV2Pool.CurveV2PoolData({
            pool: 0xD51a44d3FaE010294C616388b506AcdA1bfAAE46,
            fromTokenIndex: 0,
            toTokenIndex: 2
        });
    }

    function uniswapV3Path()
        internal
        pure
        override(SettlerPairTest, AllowanceHolderPairTest, SettlerMetaTxnPairTest, UniswapV3PairTest, ZeroExPairTest)
        returns (bytes memory)
    {
        return abi.encodePacked(fromToken(), uint24(500), toToken());
    }

    function uniswapV2Path() internal pure override(SettlerPairTest) returns (bytes memory) {
        return abi.encodePacked(fromToken(), uint8(0x80), toToken());
    }
}

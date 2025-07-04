// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {AllowanceHolderPairTest} from "./AllowanceHolderPairTest.t.sol";
import {SettlerPairTest} from "./SettlerPairTest.t.sol";
import {SettlerMetaTxnPairTest} from "./SettlerMetaTxnPairTest.t.sol";
import {UniswapV2PairTest} from "./UniswapV2PairTest.t.sol";
import {UniswapV3PairTest} from "./UniswapV3PairTest.t.sol";
import {UniswapV4PairTest} from "./UniswapV4PairTest.t.sol";
import {CurveTricryptoPairTest} from "./CurveTricryptoPairTest.t.sol";
import {ZeroExPairTest} from "./ZeroExPairTest.t.sol";
import {TokenTransferTest} from "./TokenTransferTest.t.sol";
import {CurveV2PairTest} from "./CurveV2PairTest.t.sol";
import {ICurveV2Pool} from "./vendor/ICurveV2Pool.sol";
import {SettlerBasePairTest} from "./SettlerBasePairTest.t.sol";

import {MainnetDefaultFork} from "./BaseForkTest.t.sol";

contract USDTWETHTest is
    AllowanceHolderPairTest,
    CurveV2PairTest,
    SettlerPairTest,
    SettlerMetaTxnPairTest,
    TokenTransferTest,
    UniswapV2PairTest,
    UniswapV3PairTest,
    UniswapV4PairTest,
    CurveTricryptoPairTest,
    ZeroExPairTest
{
    function setUp()
        public
        override(
            SettlerBasePairTest,
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

    function slippageLimit() internal pure override returns (uint256) {
        return 0.5 ether;
    }

    function testBlockNumber()
        internal
        pure
        virtual
        override(MainnetDefaultFork, UniswapV3PairTest)
        returns (uint256)
    {
        return super.testBlockNumber();
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

    function curveV2TricryptoPoolId() internal override returns (uint80) {
        // The CurveV2 Tricrypto factory pool actions have been disabled on Mainnet for contract size
        return super.curveV2TricryptoPoolId();
        /*
        return
        // nonce
        (
            (uint80(uint64(2)) << 16)
            // sellIndex
            | (uint80(uint8(0)) << 8)
            // buyIndex
            | uint80(uint8(2))
        );
        */
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
        return 0x0d4a11d5EEaaC28EC3F61d100daF4d40471f1852;
    }
}

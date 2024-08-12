// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "forge-std/interfaces/IERC20.sol";

import {AllowanceHolderPairTest} from "./AllowanceHolderPairTest.t.sol";
import {ZeroExPairTest} from "./ZeroExPairTest.t.sol";
import {UniswapV3PairTest} from "./UniswapV3PairTest.t.sol";
import {CurveTricryptoPairTest} from "./CurveTricryptoPairTest.t.sol";
import {DodoV1PairTest} from "./DodoV1PairTest.t.sol";
import {MaverickV2PairTest} from "./MaverickV2PairTest.t.sol";
import {SettlerBasePairTest} from "./SettlerBasePairTest.t.sol";
import {SettlerPairTest} from "./SettlerPairTest.t.sol";
import {SettlerMetaTxnPairTest} from "./SettlerMetaTxnPairTest.t.sol";
import {TokenTransferTest} from "./TokenTransferTest.t.sol";
import {Permit2TransferTest} from "./Permit2TransferTest.t.sol";

import {ICurveV2Pool} from "./vendor/ICurveV2Pool.sol";

contract USDCWETHTest is
    AllowanceHolderPairTest,
    SettlerPairTest,
    SettlerMetaTxnPairTest,
    ZeroExPairTest,
    UniswapV3PairTest,
    CurveTricryptoPairTest,
    DodoV1PairTest,
    MaverickV2PairTest,
    TokenTransferTest,
    Permit2TransferTest
{
    function setUp()
        public
        override(
            AllowanceHolderPairTest,
            SettlerBasePairTest,
            SettlerPairTest,
            SettlerMetaTxnPairTest,
            MaverickV2PairTest,
            ZeroExPairTest,
            UniswapV3PairTest,
            TokenTransferTest,
            Permit2TransferTest
        )
    {
        super.setUp();
    }

    function testName() internal pure override returns (string memory) {
        return "USDC-WETH";
    }

    function fromToken() internal pure override returns (IERC20) {
        return IERC20(0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48);
    }

    function toToken() internal pure override returns (IERC20) {
        return IERC20(0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2);
    }

    function amount() internal pure override returns (uint256) {
        return 1000e6;
    }

    function dodoV1Pool() internal pure override returns (address) {
        return 0x75c23271661d9d143DCb617222BC4BEc783eff34;
    }

    function dodoV1Direction() internal pure override returns (bool) {
        return true;
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
        return 0xB4e16d0168e52d35CaCD2c6185b44281Ec28C9Dc;
    }

    function getCurveV2PoolData()
        internal
        pure
        override(SettlerPairTest, ZeroExPairTest)
        returns (ICurveV2Pool.CurveV2PoolData memory poolData)
    {}

    function curveV2TricryptoPoolId() internal pure override returns (uint80) {
        return
        // nonce
        (
            (uint80(uint64(1)) << 16)
            // sellIndex
            | (uint80(uint8(0)) << 8)
            // buyIndex
            | uint80(uint8(2))
        );
    }

    function maverickV2Salt() internal pure override returns (bytes32) {
        uint64 feeAIn = 100000000000000;
        uint64 feeBIn = 100000000000000;
        uint16 tickSpacing = 2232;
        uint32 lookback = 3600;
        IERC20 tokenA = fromToken();
        IERC20 tokenB = toToken();
        uint8 kinds = 1;
        bytes32 salt = keccak256(abi.encode(feeAIn, feeBIn, tickSpacing, lookback, tokenA, tokenB, kinds, address(0)));
        return salt;
    }

    function maverickV2TokenAIn() internal pure override returns (bool) {
        return fromToken() < toToken();
    }
}

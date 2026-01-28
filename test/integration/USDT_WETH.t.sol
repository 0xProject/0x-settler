// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {AllowanceHolderPairTest} from "./AllowanceHolderPairTest.t.sol";
import {SettlerPairTest} from "./SettlerPairTest.t.sol";
import {SettlerMetaTxnPairTest} from "./SettlerMetaTxnPairTest.t.sol";
import {UniswapV2PairTest} from "./UniswapV2PairTest.t.sol";
import {UniswapV3PairTest} from "./UniswapV3PairTest.t.sol";
import {CurveTricryptoPairTest} from "./CurveTricryptoPairTest.t.sol";
import {ZeroExPairTest} from "./ZeroExPairTest.t.sol";
import {TokenTransferTest} from "./TokenTransferTest.t.sol";
import {CurveV2PairTest} from "./CurveV2PairTest.t.sol";
import {ICurveV2Pool} from "./vendor/ICurveV2Pool.sol";
import {SettlerBasePairTest} from "./SettlerBasePairTest.t.sol";

import {MainnetDefaultFork} from "./BaseForkTest.t.sol";
import {EkuboV3Test} from "./Ekubo.t.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";

contract USDTWETHTest is
    AllowanceHolderPairTest,
    CurveV2PairTest,
    SettlerPairTest,
    SettlerMetaTxnPairTest,
    TokenTransferTest,
    UniswapV2PairTest,
    UniswapV3PairTest,
    CurveTricryptoPairTest,
    EkuboV3Test,
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
            ZeroExPairTest,
            EkuboV3Test
        )
    {
        super.setUp();
    }

    function _testName() internal pure override returns (string memory) {
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

    function _testBlockNumber()
        internal
        pure
        virtual
        override(MainnetDefaultFork, UniswapV3PairTest)
        returns (uint256)
    {
        return super._testBlockNumber();
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
        view
        override(SettlerPairTest, AllowanceHolderPairTest, SettlerMetaTxnPairTest)
        returns (bytes memory)
    {
        return abi.encodePacked(fromToken(), uint8(0), uint24(500), sqrtPriceLimitX96FromTo(), toToken());
    }

    function uniswapV3PathCompat() internal pure override(UniswapV3PairTest, ZeroExPairTest) returns (bytes memory) {
        return abi.encodePacked(fromToken(), uint24(500), toToken());
    }

    function uniswapV2Pool() internal pure override(SettlerPairTest, AllowanceHolderPairTest) returns (address) {
        return 0x0d4a11d5EEaaC28EC3F61d100daF4d40471f1852;
    }

    function ekuboExtensionConfig() internal pure override returns (bytes32) {
        // Key for ETH_USDT pool (not WETH)
        return bytes32(0x5555ff9ff2757500bf4ee020dcfd0210cffa41be000d1b71758e219680000064);
    }

    function ekuboTokens() internal pure override returns (IERC20, IERC20) {
        return (fromToken(), ETH);
    }

    function ekuboExtraActions(bytes[] memory actions) internal view virtual override returns (bytes[] memory) {
        bytes[] memory data = new bytes[](actions.length + 2);
        address _weth = address(toToken());
        for (uint256 i; i < actions.length; i++) {
            data[i] = actions[i];
        }
        data[actions.length] = abi.encodeCall(ISettlerActions.BASIC, (address(ETH), 10_000, address(_weth), 0, ""));
        data[actions.length + 1] = abi.encodeCall(
            ISettlerActions.BASIC,
            (_weth, 10_000, address(_weth), 36, abi.encodeCall(toToken().transfer, (FROM, uint256(0))))
        );
        return data;
    }

    function recipient() internal view virtual override returns (address) {
        return address(settler);
    }
}

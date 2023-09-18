// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {ERC20} from "solmate/src/tokens/ERC20.sol";

import {ZeroExPairTest} from "./ZeroExPairTest.t.sol";
import {UniswapV3PairTest} from "./UniswapV3PairTest.t.sol";
import {SettlerPairTest} from "./SettlerPairTest.t.sol";
import {TokenTransferTest} from "./TokenTransferTest.t.sol";

import {ICurveV2Pool} from "./vendor/ICurveV2Pool.sol";

contract DAIWETHTest is SettlerPairTest, TokenTransferTest, UniswapV3PairTest, ZeroExPairTest {
    function setUp() public override(SettlerPairTest, TokenTransferTest, UniswapV3PairTest, ZeroExPairTest) {
        super.setUp();
    }

    function testName() internal pure override returns (string memory) {
        return "DAI-WETH";
    }

    function fromToken() internal pure override returns (ERC20) {
        return ERC20(0x6B175474E89094C44Da98b954EedeAC495271d0F);
    }

    function toToken() internal pure override returns (ERC20) {
        return ERC20(0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2);
    }

    function amount() internal pure override returns (uint256) {
        return 1000e18;
    }

    function uniswapV3Path()
        internal
        pure
        override(SettlerPairTest, UniswapV3PairTest, ZeroExPairTest)
        returns (bytes memory)
    {
        return abi.encodePacked(fromToken(), uint24(500), toToken());
    }

    function uniswapV2Path() internal pure override(SettlerPairTest) returns (bytes memory) {
        return abi.encodePacked(fromToken(), uint8(0), toToken());
    }

    function getCurveV2PoolData()
        internal
        pure
        override(SettlerPairTest, ZeroExPairTest)
        returns (ICurveV2Pool.CurveV2PoolData memory poolData)
    {}
}

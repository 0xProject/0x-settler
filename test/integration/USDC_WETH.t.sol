// SPDX-License-Identifier: MIT
pragma solidity ^0.8.17;

import {ERC20} from "solmate/src/tokens/ERC20.sol";

import {ZeroExPairTest} from "./ZeroExPairTest.t.sol";
import {UniswapV3PairTest} from "./UniswapV3PairTest.t.sol";
import {SettlerPairTest} from "./SettlerPairTest.t.sol";
import {TokenTransferTest} from "./TokenTransferTest.t.sol";

contract USDCWETHTest is ZeroExPairTest, UniswapV3PairTest, SettlerPairTest, TokenTransferTest {
    function testName() internal pure override returns (string memory) {
        return "USDC-WETH";
    }

    function fromToken() internal pure override returns (ERC20) {
        return ERC20(0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48);
    }

    function toToken() internal pure override returns (ERC20) {
        return ERC20(0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2);
    }

    function amount() internal pure override returns (uint256) {
        return 1000e6;
    }

    function uniswapV3Path()
        internal
        pure
        override(ZeroExPairTest, UniswapV3PairTest, SettlerPairTest)
        returns (bytes memory)
    {
        return abi.encodePacked(fromToken(), uint24(500), toToken());
    }
}

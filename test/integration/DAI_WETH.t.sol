// SPDX-License-Identifier: MIT
pragma solidity ^0.8.17;

import {ERC20} from "solmate/src/tokens/ERC20.sol";

import {TokenPairTest} from "./TokenPairTest.t.sol";

contract USDCWETHTest is TokenPairTest {
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

    function uniswapV3Path() internal pure override returns (bytes memory) {
        return abi.encodePacked(fromToken(), uint24(500), toToken());
    }
}

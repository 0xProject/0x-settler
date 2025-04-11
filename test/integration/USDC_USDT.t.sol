// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {IERC4626} from "@forge-std/interfaces/IERC4626.sol";

import {BalancerV3Test} from "./BalancerV3.t.sol";
import {EkuboTest} from "./Ekubo.t.sol";

contract USDCUSDTTest is BalancerV3Test, EkuboTest {
    function setUp() public override(BalancerV3Test, EkuboTest) {
        super.setUp();
    }

    function balancerV3Pool() internal pure override returns (address) {
        // Aave-boosted USDC/USDT
        return 0x89BB794097234E5E930446C0CeC0ea66b35D7570;
    }

    function fromTokenWrapped() internal pure override returns (IERC4626) {
        return IERC4626(0xD4fa2D31b7968E448877f69A96DE69f5de8cD23E); // aUSDC
    }

    function toTokenWrapped() internal pure override returns (IERC4626) {
        return IERC4626(0x7Bc3485026Ac48b6cf9BaF0A377477Fff5703Af8); // aUSDT
    }

    function testName() internal pure override returns (string memory) {
        return "USDC-USDT";
    }

    function fromToken() internal pure override returns (IERC20) {
        return IERC20(0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48); // USDC
    }

    function toToken() internal pure override returns (IERC20) {
        return IERC20(0xdAC17F958D2ee523a2206206994597C13D831ec7); // USDT
    }

    function amount() internal pure override returns (uint256) {
        return 1000e6;
    }

    function uniswapV3Path() internal pure override returns (bytes memory) {
        return "";
    }

    function uniswapV2Pool() internal pure override returns (address) {
        return address(0);
    }

    function ekuboPoolConfig() internal pure override returns (bytes32) {
        return bytes32(0x00000000000000000000000000000000000000000000a7c5ac471b4700000032);
    }
}

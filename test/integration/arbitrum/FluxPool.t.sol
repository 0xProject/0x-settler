// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {RobinHoodSettler} from "src/chains/RobinHood/TakerSubmitted.sol";
import {FluxPoolTest} from "../FluxPool.t.sol";

contract RobinHoodFluxPoolTest is FluxPoolTest {
    function _testName() internal pure override returns (string memory) {
        return "WETH-USDG";
    }

    function _testChainId() internal pure override returns (string memory) {
        return "robinhood";
    }

    function _testBlockNumber() internal pure override returns (uint256) {
        return 69485086;
    }

    function fromToken() internal pure override returns (IERC20) {
        return IERC20(0x0Bd7D308f8E1639FAb988df18A8011f41EAcAD73); // WETH
    }

    function toToken() internal pure override returns (IERC20) {
        return IERC20(0x5fc5360D0400a0Fd4f2af552ADD042D716F1d168); // USDG
    }

    function amount() internal pure override returns (uint256) {
        return 0.001 ether;
    }

    function settlerInitCode() internal pure override returns (bytes memory) {
        return bytes.concat(type(RobinHoodSettler).creationCode, abi.encode(bytes20(0)));
    }

    function fluxFeeManager() internal pure override returns (address) {
        return 0xe3F20402258FfE233c1172f04F38635C8D95716b;
    }

    function poolId() internal pure override returns (bytes32) {
        return 0xa6e7001ac466522854f6f477bd3556330db73450120b99d5268780c24dfb6d6d;
    }

    function expectedAmountOut() internal pure override returns (uint256) {
        return 2726566;
    }
}

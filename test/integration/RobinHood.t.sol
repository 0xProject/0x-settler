// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {BebopPairTest} from "./BebopPairTest.t.sol";
import {BasePairTest} from "./BasePairTest.t.sol";
import {MainnetDefaultFork} from "./BaseForkTest.t.sol";
import {OrvexCLTest} from "./OrvexCL.t.sol";
import {PancakeInfinityTest} from "./PancakeInfinity.t.sol";
import {SettlerBasePairTest} from "./SettlerBasePairTest.t.sol";
import {RobinHoodSettler} from "src/chains/RobinHood/TakerSubmitted.sol";
import {RobinHoodSettlerMetaTxn} from "src/chains/RobinHood/MetaTxn.sol";
import {
    pancakeInfinityRobinHoodVault,
    pancakeInfinityRobinHoodClManager,
    pancakeInfinityRobinHoodClManagerId
} from "src/core/pancakeInfinityForks/PancakeInfinityRobinHood.sol";

contract RobinHoodWETHNVDATest is BebopPairTest, OrvexCLTest {
    function setUp() public override(PancakeInfinityTest, BebopPairTest) {
        super.setUp();
    }

    function _testBlockNumber() internal pure override(MainnetDefaultFork, OrvexCLTest) returns (uint256) {
        return super._testBlockNumber();
    }

    function _testChainId() internal pure override(MainnetDefaultFork, OrvexCLTest) returns (string memory) {
        return super._testChainId();
    }

    function settlerInitCode() internal override(OrvexCLTest, SettlerBasePairTest) returns (bytes memory) {
        return super.settlerInitCode();
    }

    function sqrtPriceLimitX96(IERC20 sellToken, IERC20 buyToken)
        internal
        view
        override(BasePairTest, PancakeInfinityTest)
        returns (uint160)
    {
        return super.sqrtPriceLimitX96(sellToken, buyToken);
    }

    function pancakeInfinityForkName() internal pure override returns (string memory) {
        return "orvex";
    }

    function _testName() internal pure override returns (string memory) {
        return "WETH-NVDA";
    }

    function fromToken() internal pure override returns (IERC20) {
        return IERC20(0x0Bd7D308f8E1639FAb988df18A8011f41EAcAD73); // WETH
    }

    function toToken() internal pure override returns (IERC20) {
        return IERC20(0xd0601CE157Db5bdC3162BbaC2a2C8aF5320D9EEC); // NVDA
    }

    function poolId() internal view virtual override returns (bytes32) {
        return bytes32(0x257df135116403937e4b04b22b796e6746d965090fef574b684c9c294c542490);
    }

    function amount() internal view virtual override returns (uint256) {
        return 0.1 ether;
    }
}

contract RobinHoodWETHUSDGTest is PancakeInfinityTest {
    function setUp() public override {
        super.setUp();

        // FROM has code at this block; clear it so Permit2 verifies the EOA signature with ecrecover.
        vm.etch(FROM, "");
        vm.makePersistent(FROM);
    }

    function _testBlockNumber() internal pure override returns (uint256) {
        return 60170000;
    }

    function _testChainId() internal pure override returns (string memory) {
        return "robinhood";
    }

    function settlerInitCode() internal pure override returns (bytes memory) {
        return bytes.concat(type(RobinHoodSettler).creationCode, abi.encode(bytes20(0)));
    }

    function settlerMetaTxnInitCode() internal pure override returns (bytes memory) {
        return bytes.concat(type(RobinHoodSettlerMetaTxn).creationCode, abi.encode(bytes20(0)));
    }

    function vault() internal pure override returns (address) {
        return pancakeInfinityRobinHoodVault;
    }

    function clPoolManager() internal pure override returns (address) {
        return pancakeInfinityRobinHoodClManager;
    }

    function binPoolManager() internal pure override returns (address) {
        return address(0);
    }

    function poolManagerId() internal pure override returns (uint8) {
        return pancakeInfinityRobinHoodClManagerId;
    }

    function _testName() internal pure override returns (string memory) {
        return "WETH-USDG";
    }

    function fromToken() internal pure override returns (IERC20) {
        return IERC20(0x0Bd7D308f8E1639FAb988df18A8011f41EAcAD73);
    }

    function toToken() internal pure override returns (IERC20) {
        return IERC20(0x5fc5360D0400a0Fd4f2af552ADD042D716F1d168);
    }

    function poolId() internal pure override returns (bytes32) {
        return 0xdde13ccbbcd10c5fc3351c284eabc77114d2a88078eb1cfd20062124e939d4cf;
    }

    function amount() internal pure override returns (uint256) {
        return 0.1 ether;
    }
}

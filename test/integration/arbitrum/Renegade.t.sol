// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ARBITRUM_SELECTOR} from "src/core/Renegade.sol";
import {ArbitrumSettler} from "src/chains/Arbitrum/TakerSubmitted.sol";
import {
    ARBITRUM_GAS_SPONSOR,
    ARBITRUM_TXN_CALLDATA,
    ARBITRUM_TXN_BLOCK,
    ABRITRUM_USDC,
    ABRITRUM_WETH,
    ARBITRUM_AMOUNT
} from "../RenegadeTxn.t.sol";
import {RenegadeTest} from "../Renegade.t.sol";

contract RenegadeArbitrumIntegrationTest is RenegadeTest {
    function setUp() public virtual override {
        target = ARBITRUM_GAS_SPONSOR;
        txnCalldata = ARBITRUM_TXN_CALLDATA;
        selector = ARBITRUM_SELECTOR;

        super.setUp();
    }

    function settlerInitCode() internal virtual override returns (bytes memory) {
        return bytes.concat(type(ArbitrumSettler).creationCode, abi.encode(bytes20(0)));
    }

    function _testChainId() internal pure virtual override returns (string memory) {
        return "arbitrum";
    }

    function _testBlockNumber() internal pure virtual override returns (uint256) {
        return ARBITRUM_TXN_BLOCK - 1;
    }

    function fromToken() internal pure virtual override returns (IERC20) {
        return ABRITRUM_USDC;
    }

    function toToken() internal pure virtual override returns (IERC20) {
        return ABRITRUM_WETH;
    }

    function _testName() internal pure virtual override returns (string memory) {
        return "USDC-WETH";
    }

    function amount() internal pure virtual override returns (uint256) {
        return ARBITRUM_AMOUNT;
    }
}

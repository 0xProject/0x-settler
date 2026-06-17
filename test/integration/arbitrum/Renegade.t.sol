// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ArbitrumSettler} from "src/chains/Arbitrum/TakerSubmitted.sol";
import {RenegadeIntegrationTest} from "../../utils/RenegadeIntegration.sol";
import {
    ARBITRUM_AMOUNT,
    ARBITRUM_GMX,
    ARBITRUM_GAS_SPONSOR,
    ARBITRUM_TXN_BLOCK,
    ARBITRUM_TXN_CALLDATA,
    ARBITRUM_USDC
} from "../RenegadeTxn.t.sol";

contract RenegadeArbitrumIntegrationTest is RenegadeIntegrationTest {
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
        return ARBITRUM_GMX;
    }

    function toToken() internal pure virtual override returns (IERC20) {
        return ARBITRUM_USDC;
    }

    function _testName() internal pure virtual override returns (string memory) {
        return "ARBITRUM-RENEGADE";
    }

    function amount() internal pure virtual override returns (uint256) {
        return ARBITRUM_AMOUNT;
    }

    function _gasSponsor() internal pure virtual override returns (address) {
        return ARBITRUM_GAS_SPONSOR;
    }

    function _txnCalldata() internal pure virtual override returns (bytes memory) {
        return ARBITRUM_TXN_CALLDATA;
    }
}

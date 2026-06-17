// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {BaseSettler} from "src/chains/Base/TakerSubmitted.sol";
import {RenegadeIntegrationTest} from "../utils/RenegadeIntegration.sol";
import {
    BASE_AMOUNT,
    BASE_GAS_SPONSOR,
    BASE_TXN_BLOCK,
    BASE_TXN_CALLDATA,
    BASE_USDC,
    BASE_WETH
} from "./RenegadeTxn.t.sol";

contract RenegadeBaseIntegrationTest is RenegadeIntegrationTest {
    function settlerInitCode() internal virtual override returns (bytes memory) {
        return bytes.concat(type(BaseSettler).creationCode, abi.encode(bytes20(0)));
    }

    function _testChainId() internal pure virtual override returns (string memory) {
        return "base";
    }

    function _testBlockNumber() internal pure virtual override returns (uint256) {
        return BASE_TXN_BLOCK - 1;
    }

    function fromToken() internal pure virtual override returns (IERC20) {
        return BASE_USDC;
    }

    function toToken() internal pure virtual override returns (IERC20) {
        return BASE_WETH;
    }

    function _testName() internal pure virtual override returns (string memory) {
        return "BASE-RENEGADE";
    }

    function amount() internal pure virtual override returns (uint256) {
        return BASE_AMOUNT;
    }

    function _gasSponsor() internal pure virtual override returns (address) {
        return BASE_GAS_SPONSOR;
    }

    function _txnCalldata() internal pure virtual override returns (bytes memory) {
        return BASE_TXN_CALLDATA;
    }

    // minBuyAmount == the gross quote passes the pre-call check, so the post-call check (net of
    // relayer/protocol fees) is what reverts.
    function testPostCallSlippageRevert() public {
        uint256 gross = (BASE_AMOUNT << 63) / _price(BASE_TXN_CALLDATA);
        _expectSlippageRevert(_buildExecData(BASE_TXN_CALLDATA, gross));
    }

    // Inner minBuyAmount == 0, yet the outer AllowedSlippage still binds against the actual receipt.
    function testOuterSlippageBindsWhenInnerMinIsZero() public {
        uint256 gross = (BASE_AMOUNT << 63) / _price(BASE_TXN_CALLDATA);
        _expectSlippageRevert(_buildExecData(BASE_TXN_CALLDATA, 0, gross));
    }
}

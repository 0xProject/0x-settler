// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {AllowanceHolderPairTest} from "./AllowanceHolderPairTest.t.sol";

import {LfjTmTest} from "./LfjTm.t.sol";

// stupid Solidity inheritance
import {MainnetDefaultFork} from "./BaseForkTest.t.sol";
import {SettlerBasePairTest} from "./SettlerBasePairTest.t.sol";

contract testfrontWMONTest is AllowanceHolderPairTest, LfjTmTest {
    function _testName() internal pure override returns (string memory) {
        return "testfront-WMON";
    }

    function amount() internal pure override returns (uint256) {
        return 100e18;
    }

    function uniswapV3Path() internal pure override returns (bytes memory) {
        return "";
    }

    function uniswapV2Pool() internal pure override returns (address) {
        return address(0);
    }

    // stupid Solidity inheritance
    function setUp() public override(AllowanceHolderPairTest, LfjTmTest) {
        return super.setUp();
    }

    function _testBlockNumber() internal pure override(MainnetDefaultFork, LfjTmTest) returns (uint256) {
        return super._testBlockNumber();
    }

    function _testChainId() internal pure override(MainnetDefaultFork, LfjTmTest) returns (string memory) {
        return super._testChainId();
    }

    function settlerInitCode() internal override(SettlerBasePairTest, LfjTmTest) returns (bytes memory) {
        return super.settlerInitCode();
    }
}

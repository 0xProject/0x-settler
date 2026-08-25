// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {RobinHoodSettler} from "src/chains/RobinHood/TakerSubmitted.sol";
import {RobinHoodSettlerMetaTxn} from "src/chains/RobinHood/MetaTxn.sol";
import {orvexVault, orvexClManager} from "src/core/pancakeInfinityForks/OrvexCL.sol";

import {PancakeInfinityTest} from "./PancakeInfinity.t.sol";

abstract contract OrvexCLTest is PancakeInfinityTest {
    function _testBlockNumber() internal pure virtual override returns (uint256) {
        return 30443000;
    }

    function _testChainId() internal pure virtual override returns (string memory) {
        return "robinhood";
    }

    function settlerInitCode() internal virtual override returns (bytes memory) {
        return bytes.concat(type(RobinHoodSettler).creationCode, abi.encode(bytes20(0)));
    }

    function settlerMetaTxnInitCode() internal override returns (bytes memory) {
        return bytes.concat(type(RobinHoodSettlerMetaTxn).creationCode, abi.encode(bytes20(0)));
    }

    function vault() internal pure override returns (address) {
        return orvexVault;
    }

    function clPoolManager() internal pure override returns (address) {
        return orvexClManager;
    }

    // Orvex does not have a Bin pool manager
    function binPoolManager() internal pure override returns (address) {
        return address(0);
    }
}

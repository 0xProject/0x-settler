// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

abstract contract BaseForkTest {
    function _testChainId() internal view virtual returns (string memory);
    function _testBlockNumber() internal view virtual returns (uint256);
}

contract MainnetDefaultFork is BaseForkTest {
    function _testChainId() internal pure virtual override returns (string memory) {
        return "mainnet";
    }

    function _testBlockNumber() internal pure virtual override returns (uint256) {
        return 18685612;
    }
}

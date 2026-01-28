// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {ItoA} from "src/utils/ItoA.sol";

library SafeConfig {
    function _isTestnet() internal view returns (bool) {
        if (
            block.chainid == 10143 // monad testnet
                || block.chainid == 11124 // abstract sepolia
                || block.chainid == 11155111 // sepolia
        ) {
            return true;
        }
        if (
            block.chainid == 1 // mainnet
                || block.chainid == 10 // optimism
                || block.chainid == 56 // bnb
                || block.chainid == 100 // gnosis
                || block.chainid == 130 // unichain
                || block.chainid == 137 // polygon
                || block.chainid == 143 // monad
                || block.chainid == 146 // sonic
                || block.chainid == 480 // worldchain
                || block.chainid == 999 // hyperevm
                || block.chainid == 2741 // abstract
                || block.chainid == 5000 // mantle
                || block.chainid == 8453 // base
                || block.chainid == 9745 // plasma
                || block.chainid == 34443 // mode
                || block.chainid == 42161 // arbitrum
                || block.chainid == 43114 // avalanche
                || block.chainid == 57073 // ink
                || block.chainid == 59144 // linea
                || block.chainid == 80094 // berachain
                || block.chainid == 81457 // blast
                || block.chainid == 167000 // taiko
                || block.chainid == 534352 // scroll
                || block.chainid == 747474 // katana
        ) {
            return false;
        }
        revert(string.concat("Unrecognized chainid ", ItoA.itoa(block.chainid)));
    }

    function _isMainnet() internal view returns (bool) {
        if (block.chainid == 1) {
            return true;
        }
        if (
            block.chainid == 10 // optimism
                || block.chainid == 56 // bnb
                || block.chainid == 100 // gnosis
                || block.chainid == 130 // unichain
                || block.chainid == 137 // polygon
                || block.chainid == 143 // monad
                || block.chainid == 146 // sonic
                || block.chainid == 480 // worldchain
                || block.chainid == 999 // hyperevm
                || block.chainid == 2741 // abstract
                || block.chainid == 5000 // mantle
                || block.chainid == 8453 // base
                || block.chainid == 9745 // plasma
                || block.chainid == 10143 // monad testnet
                || block.chainid == 11124 // abstract sepolia
                || block.chainid == 34443 // mode
                || block.chainid == 42161 // arbitrum
                || block.chainid == 43114 // avalanche
                || block.chainid == 57073 // ink
                || block.chainid == 59144 // linea
                || block.chainid == 80094 // berachain
                || block.chainid == 81457 // blast
                || block.chainid == 167000 // taiko
                || block.chainid == 534352 // scroll
                || block.chainid == 747474 // katana
                || block.chainid == 11155111 // sepolia
        ) {
            return false;
        }
        revert(string.concat("Unrecognized chainid ", ItoA.itoa(block.chainid)));
    }

    function isEraVm() internal view returns (bool) {
        if (
            block.chainid == 2741 // abstract
                || block.chainid == 11124 // abstract sepolia
        ) {
            return true;
        }
        if (
            block.chainid == 1 // ethereum
                || block.chainid == 10 // optimism
                || block.chainid == 56 // bnb
                || block.chainid == 100 // gnosis
                || block.chainid == 130 // unichain
                || block.chainid == 137 // polygon
                || block.chainid == 146 // sonic
                || block.chainid == 480 // worldchain
                || block.chainid == 999 // hyperevm
                || block.chainid == 5000 // mantle
                || block.chainid == 8453 // base
                || block.chainid == 9745 // plasma
                || block.chainid == 10143 // monad testnet
                || block.chainid == 34443 // mode
                || block.chainid == 42161 // arbitrum
                || block.chainid == 43114 // avalanche
                || block.chainid == 57073 // ink
                || block.chainid == 59144 // linea
                || block.chainid == 80094 // berachain
                || block.chainid == 81457 // blast
                || block.chainid == 167000 // taiko
                || block.chainid == 534352 // scroll
                || block.chainid == 747474 // katana
                || block.chainid == 11155111 // sepolia
        ) {
            return false;
        }
        revert(string.concat("Unrecognized chainid ", ItoA.itoa(block.chainid)));
    }

    uint256 internal constant upgradeSafeThreshold = 2;

    function getUpgradeSafeSigners() internal view returns (address[] memory) {
        address[] memory result = new address[](4);
        result[0] = 0x257619B7155d247e43c8B6d90C8c17278Ae481F0; // Will
        result[1] = 0x3C3a57b5CC72933E312e0b0bEBe031F72d47c30B; // Duncan
        if (_isMainnet()) {
            result[2] = 0x5ee2a00F8f01d099451844Af7F894f26A57FCbF2; // Amir
            result[3] = 0x269984C978bFA5693D5915201e4dd1B7686aA6F7; // Jacob
        } else {
            result[2] = 0x9E4496adE6096b000C856219C27734F4f89A5210; // Amir
            result[3] = 0x5A9d540A07a96a2bfC8a8dfd638359778C72526f; // Jacob
        }
        return result;
    }

    uint256 internal constant deploymentSafeThreshold = 2;

    // forgefmt: disable-next-line
    function getDeploymentSafeSigners() internal view returns (address[] memory) { // this is non-pure (view) on purpose
        address[] memory result = new address[](6);
        result[0] = 0x24420bC8C760787F3eEF3b809e81f44d31a9c5A2; // Jacob
        result[1] = 0x052809d05DC83F317b2f578710411e6cbF88AC5a; // Josh
        result[2] = 0xDCa4ee0070b4aa44b30D8af22F3CBbb2cC859dAf; // Kevin
        result[3] = 0xD6B66609E5C05210BE0A690aB3b9788BA97aFa60; // Duncan
        result[4] = 0xEC3E1F7aC9Df42c31570b02068f2e7500915e557; // Andy
        result[5] = 0x36b7E0738fe11f05d26dA55d10eE679e684e06f4; // Lazaro
        return result;
    }
}

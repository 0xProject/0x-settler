// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {ItoA} from "src/utils/ItoA.sol";

library SafeConfig {
    function _isTestnet() internal view returns (bool) {
        if (
            block.chainid == 11155111 // sepolia
                || block.chainid == 84532 // base sepolia
        ) {
            return true;
        }
        if (
            block.chainid == 1 // mainnet
                || block.chainid == 10 // optimism
                || block.chainid == 56 // bnb
                || block.chainid == 137 // polygon
                || block.chainid == 8453 // base
                || block.chainid == 42161 // arbitrum
                || block.chainid == 43114 // avalanche
                || block.chainid == 81457 // blast
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
                || block.chainid == 137 // polygon
                || block.chainid == 8453 // base
                || block.chainid == 42161 // arbitrum
                || block.chainid == 43114 // avalanche
                || block.chainid == 81457 // blast
                || block.chainid == 84532 // base sepolia
                || block.chainid == 11155111 // sepolia
        ) {
            return false;
        }
        revert(string.concat("Unrecognized chainid ", ItoA.itoa(block.chainid)));
    }

    uint256 internal constant upgradeSafeThreshold = 3;

    function getUpgradeSafeSigners() internal view returns (address[] memory) {
        address[] memory result = new address[](6);
        result[0] = 0x257619B7155d247e43c8B6d90C8c17278Ae481F0; // Will
        result[1] = 0xD88a4aFCEC49e6BFd18d1eb405259296657332e2; // Theo
        result[2] = 0xD6B66609E5C05210BE0A690aB3b9788BA97aFa60; // Duncan
        if (_isMainnet()) {
            result[3] = 0x5ee2a00F8f01d099451844Af7F894f26A57FCbF2; // Amir
            result[4] = 0x269984C978bFA5693D5915201e4dd1B7686aA6F7; // Jacob
            result[5] = 0x2b3C8B6809d3b3bb4e2a667ba5A5b4ccdAe23DA4; // Phil
        } else {
            result[3] = 0x9E4496adE6096b000C856219C27734F4f89A5210; // Amir
            result[4] = 0x5A9d540A07a96a2bfC8a8dfd638359778C72526f; // Jacob
            result[5] = 0xe982f56B645E9858e865F8335Af157e9E6e12F9e; // Phil
        }
        return result;
    }

    uint256 internal constant deploymentSafeThreshold = 2;

    function getDeploymentSafeSigners() internal view returns (address[] memory) {
        address[] memory result = new address[](7);
        result[0] = 0x24420bC8C760787F3eEF3b809e81f44d31a9c5A2; // Jacob
        result[1] = 0x000000c397124D0375555F435e201F83B636C26C; // Kyu
        result[2] = 0x6879fAb591ed0d62537A3Cac9D7cd41218445a84; // Sav
        result[3] = 0x755588A2422E4779aC30cBD3774BBB12521d2c15; // Josh
        result[4] = 0xDCa4ee0070b4aa44b30D8af22F3CBbb2cC859dAf; // Kevin
        result[5] = 0xD6B66609E5C05210BE0A690aB3b9788BA97aFa60; // Duncan
        result[6] = 0xEC3E1F7aC9Df42c31570b02068f2e7500915e557; // Andy
        return result;
    }
}

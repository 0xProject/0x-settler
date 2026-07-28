// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

// Holds the configuration that MockDoubleCallbackTarget uses for its two
// re-entrant transferFrom callbacks. 
contract MockCallbackConfig {
    uint256 public amount1;
    uint256 public amount2;
    address public token;
    address public owner;
    address public recipient;
}

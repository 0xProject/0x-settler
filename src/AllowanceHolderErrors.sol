// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

/// @notice Thrown when validating the caller against the expected caller
error InvalidSender();

/// @notice Thrown when validating the target, avoiding executing against an ERC20 directly
error ConfusedDeputy();

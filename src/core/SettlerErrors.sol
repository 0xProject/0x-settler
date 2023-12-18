// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

/// @notice Thrown when an offset is not the expected value
error InvalidOffset();

/// @notice Thrown when a validating a target contract to avoid certain types of targets
error ConfusedDeputy();

/// @notice Thrown when a target contract is invalid given the context
error InvalidTarget();

/// @notice Thrown when validating the caller against the expected caller
error InvalidSender();

/// @notice Thrown in cases when using a Trusted Forwarder / AllowanceHolder is not allowed
error ForwarderNotAllowed();

/// @notice Thrown when a signature length is not the expected length
error InvalidSignatureLen();

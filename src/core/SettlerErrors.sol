// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

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

/// @notice Thrown when a slippage limit is exceeded
error TooMuchSlippage(address token, uint256 expected, uint256 actual);

/// @notice Thrown when an AllowanceHolder transfer's permit is past its deadline
error SignatureExpired(uint256 deadline);

/// @notice An internal error that should never be thrown. Thrown when a callback-requiring
///         liquidity source makes a callback on Settler from an unexpected address.
error ReentrantCallback(address oldOperator);

/// @notice An internal error that should never be thrown. Thrown when a callback-requiring
///         liquidity source is called, but Settler never receives the callback.
error OperatorNotSpent(address oldOperator);

/// @notice An internal error that should never be thrown. This error can only be thrown by
///         non-metatx-supporting Settler instances. Thrown when a callback-requiring liquidity
///         source is called, but Settler never receives the callback.
error CallbackNotSpent(uint256 callbackInt);

/// @notice Thrown when a metatransaction has reentrancy. Metatransactions allow reentrancy in some
///         limited cases.
error ReentrantMetatransaction(bytes32 oldWitness);

/// @notice An internal error that should never be thrown. Thrown when a metatransaction fails to
///         spend a coupon.
error WitnessNotSpent(bytes32 oldWitness);

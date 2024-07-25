// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "forge-std/interfaces/IERC20.sol";

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
error TooMuchSlippage(IERC20 token, uint256 expected, uint256 actual);

/// @notice Thrown when a byte array that is supposed to encode a function from ISettlerActions is
///         not recognized in context.
error ActionInvalid(uint256 i, bytes4 action, bytes data);

/// @notice Thrown when the encoded fork ID as part of UniswapV3 fork path is not on the list of
///         recognized forks for this chain.
error UnknownForkId(uint8 forkId);

/// @notice Thrown when an AllowanceHolder transfer's permit is past its deadline
error SignatureExpired(uint256 deadline);

/// @notice An internal error that should never be thrown. Thrown when a callback reenters the
///         entrypoint and attempts to clobber the existing callback.
error ReentrantCallback(uint256 callbackInt);

/// @notice An internal error that should never be thrown. This error can only be thrown by
///         non-metatx-supporting Settler instances. Thrown when a callback-requiring liquidity
///         source is called, but Settler never receives the callback.
error CallbackNotSpent(uint256 callbackInt);

/// @notice Thrown when a metatransaction has reentrancy.
error ReentrantMetatransaction(bytes32 oldWitness);

/// @notice Thrown when any transaction has reentrancy, not just taker-submitted or metatransaction.
error ReentrantPayer(address oldPayer);

/// @notice An internal error that should never be thrown. Thrown when a metatransaction fails to
///         spend a coupon.
error WitnessNotSpent(bytes32 oldWitness);

/// @notice An internal error that should never be thrown. Thrown when the payer is unset
///         unexpectedly.
error PayerSpent();

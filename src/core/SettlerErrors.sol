// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

/// @notice Thrown when an offset is not the expected value
error InvalidOffset();

/// @notice Thrown when a validating a target contract to avoid certain types of targets
error ConfusedDeputy();

function revertConfusedDeputy() pure {
    assembly ("memory-safe") {
        mstore(0x00, 0xe758b8d5) // selector for `ConfusedDeputy()`
        revert(0x1c, 0x04)
    }
}

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

function revertTooMuchSlippage(IERC20 buyToken, uint256 expectedBuyAmount, uint256 actualBuyAmount) pure {
    assembly ("memory-safe") {
        mstore(0x54, actualBuyAmount)
        mstore(0x34, expectedBuyAmount)
        mstore(0x14, buyToken)
        mstore(0x00, 0x97a6f3b9000000000000000000000000) // selector for `TooMuchSlippage(address,uint256,uint256)` with `buyToken`'s padding
        revert(0x10, 0x64)
    }
}

/// @notice Thrown when a byte array that is supposed to encode a function from ISettlerActions is
///         not recognized in context.
error ActionInvalid(uint256 i, bytes4 action, bytes data);

function revertActionInvalid(uint256 i, uint256 action, bytes calldata data) pure {
    assembly ("memory-safe") {
        let ptr := mload(0x40)
        mstore(ptr, 0x3c74eed6) // selector for `ActionInvalid(uint256,bytes4,bytes)`
        mstore(add(0x20, ptr), i)
        mstore(add(0x40, ptr), shl(0xe0, action)) // align as `bytes4`
        mstore(add(0x60, ptr), 0x60) // offset to the length slot of the dynamic value `data`
        mstore(add(0x80, ptr), data.length)
        calldatacopy(add(0xa0, ptr), data.offset, data.length)
        revert(add(0x1c, ptr), add(0x84, data.length))
    }
}

/// @notice Thrown when the encoded fork ID as part of UniswapV3 fork path is not on the list of
///         recognized forks for this chain.
error UnknownForkId(uint8 forkId);

function revertUnknownForkId(uint8 forkId) pure {
    assembly ("memory-safe") {
        mstore(0x00, 0xd3b1276d) // selector for `UnknownForkId(uint8)`
        mstore(0x20, and(0xff, forkId))
        revert(0x1c, 0x24)
    }
}

/// @notice Thrown when an AllowanceHolder transfer's permit is past its deadline
error SignatureExpired(uint256 deadline);

/// @notice Thrown when selling the native asset, but `msg.value` exceeds the value from the generated quote
error MsgValueMismatch(uint256 expected, uint256 actual);

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

error DeltaNotPositive(IERC20 token);
error DeltaNotNegative(IERC20 token);
error ZeroSellAmount(IERC20 token);
error ZeroBuyAmount(IERC20 buyToken);
error BoughtSellToken(IERC20 sellToken);
error TokenHashCollision(IERC20 token0, IERC20 token1);
error ZeroToken();

/// @notice Thrown for liquidities that require a Newton-Raphson approximation to solve their
///         constant function when Newton-Raphson fails to converge on the solution in a
///         "reasonable" number of iterations.
error NotConverged();

/// @notice Thrown when the encoded pool manager ID as part of PancakeSwap Infinity fill is not on
///         the list of recognized pool managers.
error UnknownPoolManagerId(uint8 poolManagerId);

/// @notice Thrown when the `msg.value` is less than the minimum expected value.
error Underpayment(uint256 msgValueMin, uint256 msgValueActual);

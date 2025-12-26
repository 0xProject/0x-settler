// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

/// @title InputValidation
/// @notice Reusable library for common input validation checks across the codebase
/// @dev Provides gas-efficient validation helpers with clear error messages
library InputValidation {
    /// @notice Error thrown when an address is the zero address
    error ZeroAddress();
    
    /// @notice Error thrown when an amount is zero
    error ZeroAmount();
    
    /// @notice Error thrown when basis points exceed the maximum allowed value
    error BasisPointsExceedMax(uint256 bps, uint256 max);

    /// @notice Validates that an address is not the zero address
    /// @param addr The address to validate
    /// @dev Reverts with ZeroAddress if addr is address(0)
    function requireNonZeroAddress(address addr) internal pure {
        if (addr == address(0)) {
            revert ZeroAddress();
        }
    }

    /// @notice Validates that a token address is not the zero address
    /// @param token The token to validate
    /// @dev Reverts with ZeroAddress if token is address(0)
    function requireNonZeroToken(IERC20 token) internal pure {
        if (address(token) == address(0)) {
            revert ZeroAddress();
        }
    }

    /// @notice Validates that an amount is not zero
    /// @param amount The amount to validate
    /// @dev Reverts with ZeroAmount if amount is 0
    function requireNonZeroAmount(uint256 amount) internal pure {
        if (amount == 0) {
            revert ZeroAmount();
        }
    }

    /// @notice Validates that basis points do not exceed the maximum allowed value
    /// @param bps The basis points value to validate
    /// @param maxBps The maximum allowed basis points (typically 10000)
    /// @dev Reverts with BasisPointsExceedMax if bps > maxBps
    function requireValidBasisPoints(uint256 bps, uint256 maxBps) internal pure {
        if (bps > maxBps) {
            revert BasisPointsExceedMax(bps, maxBps);
        }
    }

    /// @notice Validates that basis points are both non-zero and within the allowed range
    /// @param bps The basis points value to validate
    /// @param maxBps The maximum allowed basis points (typically 10000)
    /// @dev Reverts with ZeroAmount if bps is 0, or BasisPointsExceedMax if bps > maxBps
    function requireNonZeroValidBasisPoints(uint256 bps, uint256 maxBps) internal pure {
        requireNonZeroAmount(bps);
        requireValidBasisPoints(bps, maxBps);
    }

    /// @notice Validates that an array is not empty
    /// @param length The length of the array to validate
    /// @dev Reverts with ZeroAmount if length is 0
    function requireNonEmptyArray(uint256 length) internal pure {
        if (length == 0) {
            revert ZeroAmount();
        }
    }

    /// @notice Validates that two addresses are not the same
    /// @param addr1 First address to compare
    /// @param addr2 Second address to compare
    /// @dev Reverts if addr1 == addr2
    error DuplicateAddress(address addr);
    
    function requireDifferentAddresses(address addr1, address addr2) internal pure {
        if (addr1 == addr2) {
            revert DuplicateAddress(addr1);
        }
    }

    /// @notice Validates that a deadline has not passed
    /// @param deadline The deadline timestamp to check
    /// @dev Reverts if block.timestamp > deadline
    error DeadlineExpired(uint256 deadline, uint256 timestamp);
    
    function requireNotExpired(uint256 deadline) internal view {
        if (block.timestamp > deadline) {
            revert DeadlineExpired(deadline, block.timestamp);
        }
    }
}

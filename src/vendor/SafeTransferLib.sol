// SPDX-License-Identifier: AGPL-3.0-only
pragma solidity >=0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

/// @notice Safe ETH and ERC20 transfer library that gracefully handles missing return values.
/// @author Solmate (https://github.com/transmissions11/solmate/blob/main/src/utils/SafeTransferLib.sol)
/// @dev Use with caution! Some functions in this library knowingly create dirty bits at the destination of the free memory pointer.
/// @dev Note that none of the functions in this library check that a token has code at all! That responsibility is delegated to the caller.
library SafeTransferLib {
    uint32 private constant _TRANSFER_FROM_FAILED_SELECTOR = 0x7939f424; // bytes4(keccak256("TransferFromFailed()"))
    uint32 private constant _TRANSFER_FAILED_SELECTOR = 0x90b8ec18; // bytes4(keccak256("TransferFailed()"))
    uint32 private constant _APPROVE_FAILED_SELECTOR = 0x3e3f8f73; // bytes4(keccak256("ApproveFailed()"))

    /*//////////////////////////////////////////////////////////////
                             ETH OPERATIONS
    //////////////////////////////////////////////////////////////*/

    function safeTransferETH(address payable to, uint256 amount) internal {
        assembly ("memory-safe") {
            // Transfer the ETH and store if it succeeded or not.
            if iszero(call(gas(), to, amount, 0, 0, 0, 0)) {
                let freeMemoryPointer := mload(0x40)
                returndatacopy(freeMemoryPointer, 0, returndatasize())
                revert(freeMemoryPointer, returndatasize())
            }
        }
    }

    /*//////////////////////////////////////////////////////////////
                            ERC20 OPERATIONS
    //////////////////////////////////////////////////////////////*/

    function safeTransferFrom(IERC20 token, address from, address to, uint256 amount) internal {
        assembly ("memory-safe") {
            // Get a pointer to some free memory.
            let freeMemoryPointer := mload(0x40)

            // Write the abi-encoded calldata into memory, beginning with the function selector.
            mstore(freeMemoryPointer, 0x23b872dd00000000000000000000000000000000000000000000000000000000)
            mstore(add(freeMemoryPointer, 4), and(from, 0xffffffffffffffffffffffffffffffffffffffff)) // Append and mask the "from" argument.
            mstore(add(freeMemoryPointer, 36), and(to, 0xffffffffffffffffffffffffffffffffffffffff)) // Append and mask the "to" argument.
            mstore(add(freeMemoryPointer, 68), amount) // Append the "amount" argument. Masking not required as it's a full 32 byte type.

            // We use 100 because the length of our calldata totals up like so: 4 + 32 * 3.
            // We use 0 and 32 to copy up to 32 bytes of return data into the scratch space.
            if iszero(call(gas(), token, 0, freeMemoryPointer, 100, 0, 32)) {
                returndatacopy(freeMemoryPointer, 0, returndatasize())
                revert(freeMemoryPointer, returndatasize())
            }
            // We check that the call either returned exactly 1 (can't just be non-zero data), or had no
            // return data.
            if iszero(or(and(eq(mload(0), 1), gt(returndatasize(), 31)), iszero(returndatasize()))) {
                mstore(0, _TRANSFER_FROM_FAILED_SELECTOR)
                revert(0x1c, 0x04)
            }
        }
    }

    function safeTransfer(IERC20 token, address to, uint256 amount) internal {
        assembly ("memory-safe") {
            // Get a pointer to some free memory.
            let freeMemoryPointer := mload(0x40)

            // Write the abi-encoded calldata into memory, beginning with the function selector.
            mstore(freeMemoryPointer, 0xa9059cbb00000000000000000000000000000000000000000000000000000000)
            mstore(add(freeMemoryPointer, 4), and(to, 0xffffffffffffffffffffffffffffffffffffffff)) // Append and mask the "to" argument.
            mstore(add(freeMemoryPointer, 36), amount) // Append the "amount" argument. Masking not required as it's a full 32 byte type.

            // We use 68 because the length of our calldata totals up like so: 4 + 32 * 2.
            // We use 0 and 32 to copy up to 32 bytes of return data into the scratch space.
            if iszero(call(gas(), token, 0, freeMemoryPointer, 68, 0, 32)) {
                returndatacopy(freeMemoryPointer, 0, returndatasize())
                revert(freeMemoryPointer, returndatasize())
            }
            // We check that the call either returned exactly 1 (can't just be non-zero data), or had no
            // return data.
            if iszero(or(and(eq(mload(0), 1), gt(returndatasize(), 31)), iszero(returndatasize()))) {
                mstore(0, _TRANSFER_FAILED_SELECTOR)
                revert(0x1c, 0x04)
            }
        }
    }

    function safeApprove(IERC20 token, address to, uint256 amount) internal {
        assembly ("memory-safe") {
            // Get a pointer to some free memory.
            let freeMemoryPointer := mload(0x40)

            // Write the abi-encoded calldata into memory, beginning with the function selector.
            mstore(freeMemoryPointer, 0x095ea7b300000000000000000000000000000000000000000000000000000000)
            mstore(add(freeMemoryPointer, 4), and(to, 0xffffffffffffffffffffffffffffffffffffffff)) // Append and mask the "to" argument.
            mstore(add(freeMemoryPointer, 36), amount) // Append the "amount" argument. Masking not required as it's a full 32 byte type.

            // We use 68 because the length of our calldata totals up like so: 4 + 32 * 2.
            // We use 0 and 32 to copy up to 32 bytes of return data into the scratch space.
            if iszero(call(gas(), token, 0, freeMemoryPointer, 68, 0, 32)) {
                returndatacopy(freeMemoryPointer, 0, returndatasize())
                revert(freeMemoryPointer, returndatasize())
            }
            // We check that the call either returned exactly 1 (can't just be non-zero data), or had no
            // return data.
            if iszero(or(and(eq(mload(0), 1), gt(returndatasize(), 31)), iszero(returndatasize()))) {
                mstore(0, _APPROVE_FAILED_SELECTOR)
                revert(0x1c, 0x04)
            }
        }
    }

    function safeApproveIfBelow(IERC20 token, address spender, uint256 amount) internal {
        uint256 allowance = token.allowance(address(this), spender);
        if (allowance < amount) {
            if (allowance != 0) {
                safeApprove(token, spender, 0);
            }
            safeApprove(token, spender, type(uint256).max);
        }
    }
}

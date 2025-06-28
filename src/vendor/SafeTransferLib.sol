// SPDX-License-Identifier: MIT
pragma solidity >=0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

/// @notice Safe ETH and ERC20 transfer library that gracefully handles missing return values.
/// @author Modified from Solady (https://github.com/vectorized/solady/blob/main/src/utils/SafeTransferLib.sol)
/// @author Modified from Solmate (https://github.com/transmissions11/solmate/blob/main/src/utils/SafeTransferLib.sol)
/// @dev Note that none of the functions in this library check that a token has code at all! That responsibility is delegated to the caller.
library SafeTransferLib {
    /*//////////////////////////////////////////////////////////////
                             ETH OPERATIONS
    //////////////////////////////////////////////////////////////*/

    function safeTransferETH(address payable to, uint256 amount) internal {
        assembly ("memory-safe") {
            // Transfer the ETH and revert if it fails.
            if iszero(call(gas(), to, amount, 0x00, 0x00, 0x00, 0x00)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
        }
    }

    /*//////////////////////////////////////////////////////////////
                            ERC20 OPERATIONS
    //////////////////////////////////////////////////////////////*/

    function fastBalanceOf(IERC20 token, address acct) internal view returns (uint256 r) {
        assembly ("memory-safe") {
            mstore(0x14, acct) // Store the `acct` argument.
            mstore(0x00, 0x70a08231000000000000000000000000) // Selector for `balanceOf(address)`, with `acct`'s padding.

            // Call and check for revert. Storing the selector with padding in
            // memory at 0 results in a start of calldata at offset 16. Calldata
            // is 36 bytes long (4 bytes selector, 32 bytes argument)
            if iszero(staticcall(gas(), token, 0x10, 0x24, 0x00, 0x20)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            // Check for short returndata and missing code
            if iszero(lt(0x1f, returndatasize())) { revert(0x00, 0x00) }

            r := mload(0x00)
        }
    }

    function safeTransferFrom(IERC20 token, address from, address to, uint256 amount) internal {
        assembly ("memory-safe") {
            let ptr := mload(0x40) // Cache the free memory pointer.

            mstore(0x60, amount) // Store the `amount` argument.
            mstore(0x40, to) // Store the `to` argument.
            mstore(0x2c, shl(0x60, from)) // Store the `from` argument. (Clears `to`'s padding.)
            mstore(0x0c, 0x23b872dd000000000000000000000000) // Selector for `transferFrom(address,address,uint256)`, with `from`'s padding.

            // Calldata starts at offset 28 and is 100 bytes long (3 * 32 + 4).
            // If there is returndata (optional) we copy the first 32 bytes into the first slot of memory.
            if iszero(call(gas(), token, 0x00, 0x1c, 0x64, 0x00, 0x20)) {
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            // We check that the call either returned exactly 1 [true] (can't just be non-zero
            // data), or had no return data.
            if iszero(or(and(eq(mload(0x00), 0x01), lt(0x1f, returndatasize())), iszero(returndatasize()))) {
                mstore(0x00, 0x7939f424) // Selector for `TransferFromFailed()`
                revert(0x1c, 0x04)
            }

            mstore(0x60, 0x00) // Restore the zero slot to zero.
            mstore(0x40, ptr) // Restore the free memory pointer.
        }
    }

    function safeTransfer(IERC20 token, address to, uint256 amount) internal {
        assembly ("memory-safe") {
            mstore(0x14, to) // Store the `to` argument.
            mstore(0x34, amount) // Store the `amount` argument.
            // Storing `amount` clobbers the upper bits of the free memory pointer, but those bits
            // can never be set without running into an OOG, so it's safe. We'll restore them to
            // zero at the end.
            mstore(0x00, 0xa9059cbb000000000000000000000000) // Selector for `transfer(address,uint256)`, with `to`'s padding.

            // Calldata starts at offset 16 and is 68 bytes long (2 * 32 + 4).
            // If there is returndata (optional) we copy the first 32 bytes into the first slot of memory.
            if iszero(call(gas(), token, 0x00, 0x10, 0x44, 0x00, 0x20)) {
                let ptr := and(0xffffff, mload(0x40))
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            // We check that the call either returned exactly 1 [true] (can't just be non-zero
            // data), or had no return data.
            if iszero(or(and(eq(mload(0x00), 0x01), lt(0x1f, returndatasize())), iszero(returndatasize()))) {
                mstore(0x00, 0x90b8ec18) // Selector for `TransferFailed()`
                revert(0x1c, 0x04)
            }

            mstore(0x34, 0x00) // Restore the part of the free memory pointer that was overwritten.
        }
    }

    function safeApprove(IERC20 token, address to, uint256 amount) internal {
        assembly ("memory-safe") {
            mstore(0x14, to) // Store the `to` argument.
            mstore(0x34, amount) // Store the `amount` argument.
            // Storing `amount` clobbers the upper bits of the free memory pointer, but those bits
            // can never be set without running into an OOG, so it's safe. We'll restore them to
            // zero at the end.
            mstore(0x00, 0x095ea7b3000000000000000000000000) // Selector for `approve(address,uint256)`, with `to`'s padding.

            // Calldata starts at offset 16 and is 68 bytes long (2 * 32 + 4).
            // If there is returndata (optional) we copy the first 32 bytes into the first slot of memory.
            if iszero(call(gas(), token, 0x00, 0x10, 0x44, 0x00, 0x20)) {
                let ptr := and(0xffffff, mload(0x40))
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            // We check that the call either returned exactly 1 [true] (can't just be non-zero
            // data), or had no return data.
            if iszero(or(and(eq(mload(0x00), 0x01), lt(0x1f, returndatasize())), iszero(returndatasize()))) {
                mstore(0x00, 0x3e3f8f73) // Selector for `ApproveFailed()`
                revert(0x1c, 0x04)
            }

            mstore(0x34, 0x00) // Restore the part of the free memory pointer that was overwritten.
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

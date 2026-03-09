// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {Take} from "./FlashAccountingCommon.sol";

type IHooks is address;

/// @dev Two `int128` values packed into a single `int256` where the upper 128 bits represent the amount0
/// and the lower 128 bits represent the amount1.
type BalanceDelta is int256;

using BalanceDeltaLibrary for BalanceDelta global;

/// @notice Library for getting the amount0 and amount1 deltas from the BalanceDelta type
library BalanceDeltaLibrary {
    function amount0(BalanceDelta balanceDelta) internal pure returns (int128 _amount0) {
        assembly ("memory-safe") {
            _amount0 := sar(0x80, balanceDelta)
        }
    }

    function amount1(BalanceDelta balanceDelta) internal pure returns (int128 _amount1) {
        assembly ("memory-safe") {
            _amount1 := signextend(0x0f, balanceDelta)
        }
    }
}

interface IPoolManager {
    /// @notice All interactions on the contract that account deltas require unlocking. A caller that calls `unlock` must implement
    /// `IUnlockCallback(msg.sender).unlockCallback(data)`, where they interact with the remaining functions on this contract.
    /// @dev The only functions callable without an unlocking are `initialize` and `updateDynamicLPFee`
    /// @param data Any data to pass to the callback, via `IUnlockCallback(msg.sender).unlockCallback(data)`
    /// @return The data returned by the call to `IUnlockCallback(msg.sender).unlockCallback(data)`
    function unlock(bytes calldata data) external returns (bytes memory);

    /// @notice Returns the key for identifying a pool
    struct PoolKey {
        /// @notice The lower token of the pool, sorted numerically
        IERC20 token0;
        /// @notice The higher token of the pool, sorted numerically
        IERC20 token1;
        /// @notice The pool LP fee, capped at 1_000_000. If the highest bit is 1, the pool has a dynamic fee and must be exactly equal to 0x800000
        uint24 fee;
        /// @notice Ticks that involve positions must be a multiple of tick spacing
        int24 tickSpacing;
        /// @notice The hooks of the pool
        IHooks hooks;
    }

    struct SwapParams {
        /// Whether to swap token0 for token1 or vice versa
        bool zeroForOne;
        /// The desired input amount if negative (exactIn), or the desired output amount if positive (exactOut)
        int256 amountSpecified;
        /// The sqrt price at which, if reached, the swap will stop executing
        uint160 sqrtPriceLimitX96;
    }

    /// @notice Swap against the given pool
    /// @param key The pool to swap in
    /// @param params The parameters for swapping
    /// @param hookData The data to pass through to the swap hooks
    /// @return swapDelta The balance delta of the address swapping
    /// @dev Swapping on low liquidity pools may cause unexpected swap amounts when liquidity available is less than amountSpecified.
    /// Additionally note that if interacting with hooks that have the BEFORE_SWAP_RETURNS_DELTA_FLAG or AFTER_SWAP_RETURNS_DELTA_FLAG
    /// the hook may alter the swap input/output. Integrators should perform checks on the returned swapDelta.
    function swap(PoolKey memory key, SwapParams memory params, bytes calldata hookData)
        external
        returns (BalanceDelta swapDelta);

    /// @notice Writes the current ERC20 balance of the specified token to transient storage
    /// This is used to checkpoint balances for the manager and derive deltas for the caller.
    /// @dev This MUST be called before any ERC20 tokens are sent into the contract, but can be skipped
    /// for native tokens because the amount to settle is determined by the sent value.
    /// However, if an ERC20 token has been synced and not settled, and the caller instead wants to settle
    /// native funds, this function can be called with the native currency to then be able to settle the native currency
    function sync(IERC20 token) external;

    /// @notice Called by the user to net out some value owed to the user
    /// @dev Can also be used as a mechanism for _free_ flash loans
    /// @param token The token to withdraw from the pool manager
    /// @param to The address to withdraw to
    /// @param amount The amount of token to withdraw
    function take(IERC20 token, address to, uint256 amount) external;

    /// @notice Called by the user to pay what is owed
    /// @return paid The amount of token settled
    function settle() external payable returns (uint256 paid);
}

/// Solc emits code that is both gas inefficient and codesize bloated. By reimplementing these
/// function calls in Yul, we obtain significant improvements. Solc also emits an EXTCODESIZE check
/// when an external function doesn't return anything (`sync`). Obviously, we know that POOL_MANAGER
/// has code, so this omits those checks. Also, for compatibility, these functions identify
/// `SettlerAbstract.ETH_ADDRESS` (the address of all `e`s) and replace it with `address(0)`.
library UnsafePoolManager {
    function unsafeSync(IPoolManager poolManager, IERC20 token) internal {
        // It is the responsibility of the calling code to determine whether `token` is
        // `ETH_ADDRESS` and substitute it with `IERC20(address(0))` appropriately. This delegation
        // of responsibility is required because a call to `unsafeSync(0)` must be followed by a
        // value-bearing call to `unsafeSettle` instead of using `IERC20.safeTransfer`
        assembly ("memory-safe") {
            mstore(0x14, token)
            mstore(0x00, 0xa5841194000000000000000000000000) // selector for `sync(address)` with `token`'s padding
            if iszero(call(gas(), poolManager, 0x00, 0x10, 0x24, 0x00, 0x00)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
        }
    }

    function unsafeSwap(
        IPoolManager poolManager,
        IPoolManager.PoolKey memory key,
        IPoolManager.SwapParams memory params,
        bytes calldata hookData
    ) internal returns (BalanceDelta r) {
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(ptr, 0xf3cd914c) // selector for `swap((address,address,uint24,int24,address),(bool,int256,uint160),bytes)`
            let token0 := mload(key)
            token0 := mul(token0, iszero(eq(0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee, token0)))
            mstore(add(0x20, ptr), token0)
            mcopy(add(0x40, ptr), add(0x20, key), 0x80)
            mcopy(add(0xc0, ptr), params, 0x60)
            mstore(add(0x120, ptr), 0x120)
            mstore(add(0x140, ptr), hookData.length)
            calldatacopy(add(0x160, ptr), hookData.offset, hookData.length)
            if iszero(call(gas(), poolManager, 0x00, add(0x1c, ptr), add(0x144, hookData.length), 0x00, 0x20)) {
                let ptr_ := mload(0x40)
                returndatacopy(ptr_, 0x00, returndatasize())
                revert(ptr_, returndatasize())
            }
            r := mload(0x00)
        }
    }

    function unsafeSettle(IPoolManager poolManager, uint256 value) internal returns (uint256 r) {
        assembly ("memory-safe") {
            mstore(0x00, 0x11da60b4) // selector for `settle()`
            if iszero(call(gas(), poolManager, value, 0x1c, 0x04, 0x00, 0x20)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            r := mload(0x00)
        }
    }

    function unsafeSettle(IPoolManager poolManager) internal returns (uint256) {
        return unsafeSettle(poolManager, 0);
    }
}

/// @notice Interface for the callback executed when an address unlocks the pool manager
interface IUnlockCallback {
    /// @notice Called by the pool manager on `msg.sender` when the manager is unlocked
    /// @param data The data that was passed to the call to unlock
    /// @return Any data that you want to be returned from the unlock call
    function unlockCallback(bytes calldata data) external returns (bytes memory);
}

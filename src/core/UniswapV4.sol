// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {SettlerAbstract} from "../SettlerAbstract.sol";

import {TooMuchSlippage} from "./SettlerErrors.sol";

type Currency is address;

/// @notice Returns the key for identifying a pool
struct PoolKey {
    /// @notice The lower currency of the pool, sorted numerically
    Currency currency0;
    /// @notice The higher currency of the pool, sorted numerically
    Currency currency1;
    /// @notice The pool LP fee, capped at 1_000_000. If the highest bit is 1, the pool has a dynamic fee and must be exactly equal to 0x800000
    uint24 fee;
    /// @notice Ticks that involve positions must be a multiple of tick spacing
    int24 tickSpacing;
    /// @notice The hooks of the pool
    IHooks hooks;
}

type PoolId is bytes32;

/// @notice Library for computing the ID of a pool
library PoolIdLibrary {
    /// @notice Returns value equal to keccak256(abi.encode(poolKey))
    function toId(PoolKey memory poolKey) internal pure returns (PoolId poolId) {
        assembly ("memory-safe") {
            // 0xa0 represents the total size of the poolKey struct (5 slots of 32 bytes)
            poolId := keccak256(poolKey, 0xa0)
        }
    }
}

using PoolIdLibrary for PoolKey global;

/// @notice Interface for the callback executed when an address unlocks the pool manager
interface IUnlockCallback {
    /// @notice Called by the pool manager on `msg.sender` when the manager is unlocked
    /// @param data The data that was passed to the call to unlock
    /// @return Any data that you want to be returned from the unlock call
    function unlockCallback(bytes calldata data) external returns (bytes memory);
}

interface IHooks {

}

interface IPoolManager {
    /// @notice Called by external contracts to access transient storage of the contract
    /// @param slot Key of slot to tload
    /// @return value The value of the slot as bytes32
    function exttload(bytes32 slot) external view returns (bytes32 value);

    /// @notice All interactions on the contract that account deltas require unlocking. A caller that calls `unlock` must implement
    /// `IUnlockCallback(msg.sender).unlockCallback(data)`, where they interact with the remaining functions on this contract.
    /// @dev The only functions callable without an unlocking are `initialize` and `updateDynamicLPFee`
    /// @param data Any data to pass to the callback, via `IUnlockCallback(msg.sender).unlockCallback(data)`
    /// @return The data returned by the call to `IUnlockCallback(msg.sender).unlockCallback(data)`
    function unlock(bytes calldata data) external returns (bytes memory);

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

    /// @notice Writes the current ERC20 balance of the specified currency to transient storage
    /// This is used to checkpoint balances for the manager and derive deltas for the caller.
    /// @dev This MUST be called before any ERC20 tokens are sent into the contract, but can be skipped
    /// for native tokens because the amount to settle is determined by the sent value.
    /// However, if an ERC20 token has been synced and not settled, and the caller instead wants to settle
    /// native funds, this function can be called with the native currency to then be able to settle the native currency
    function sync(Currency currency) external;

    /// @notice Called by the user to net out some value owed to the user
    /// @dev Can also be used as a mechanism for _free_ flash loans
    /// @param currency The currency to withdraw from the pool manager
    /// @param to The address to withdraw to
    /// @param amount The amount of currency to withdraw
    function take(Currency currency, address to, uint256 amount) external;

    /// @notice Called by the user to pay what is owed
    /// @return paid The amount of currency settled
    function settle() external payable returns (uint256 paid);

    /// @notice WARNING - Any currency that is cleared, will be non-retrievable, and locked in the contract permanently.
    /// A call to clear will zero out a positive balance WITHOUT a corresponding transfer.
    /// @dev This could be used to clear a balance that is considered dust.
    /// Additionally, the amount must be the exact positive balance. This is to enforce that the caller is aware of the amount being cleared.
    function clear(Currency currency, uint256 amount) external;
}

/// @dev Two `int128` values packed into a single `int256` where the upper 128 bits represent the amount0
/// and the lower 128 bits represent the amount1.
type BalanceDelta is int256;

/// @notice Library for getting the amount0 and amount1 deltas from the BalanceDelta type
library BalanceDeltaLibrary {
    function amount0(BalanceDelta balanceDelta) internal pure returns (int128 _amount0) {
        assembly ("memory-safe") {
            _amount0 := sar(128, balanceDelta)
        }
    }

    function amount1(BalanceDelta balanceDelta) internal pure returns (int128 _amount1) {
        assembly ("memory-safe") {
            _amount1 := signextend(15, balanceDelta)
        }
    }
}

using BalanceDeltaLibrary for BalanceDelta global;

abstract contract UniswapV4 is SettlerAbstract {
    using SafeTransferLib for IERC20;

    function sellToUniswapV4(...) internal returns (uint256) {
        return abi.decode(abi.decode(_setOperatorAndCall(address(POOL_MANAGER), abi.encodeCall(POOL_MANAGER.unlock, (abi.encode(...))), IUnlockCallback.unlockCallback.selector, unlockCallback), (bytes)), (uint256));
    }

    function _swap(PoolKey memory key, SwapParams memory params, bytes memory hookData) private DANGEROUS_freeMemory returns (BalanceDelta) {
        return poolManager.swap(
                poolKey,
                params,
                hookData
        );
    }

    uint256 private constant _HOP_LENGTH = 0;
    
    function _getPoolKey(PoolKey memory key, bytes calldata data) private pure returns (bool, bytes calldata) {
    }

    function _getHookData(bytes calldata data) private pure returns (bytes calldata, bytes calldata) {
    }

    function unlockCallback(bytes calldata data) private returns (bytes memory) {
        address payer = address(uint160(bytes20(data)));
        data = data[20:];

        IERC20 sellToken = IERC20(address(uint160(bytes20(data))));
        data = data[20:];

        uint256 sellAmount;
        // TODO: it would be really nice to be able to custody-optimize multihops by calling
        // `unlock` at the beginning of the swap and doing the dispatch loop inside the
        // callback. But this introduces additional attack surface and may not even be that much
        // more efficient considering all the `calldatacopy`ing required and memory expansion.
        if (sellToken == ETH_ADDRESS) {
            sellAmount = address(this).balance;
            // TODO: bps
            POOL_MANAGER.settle{value: sellAmount}();
            sellToken = IERC20(address(0));
        } else {
            POOL_MANAGER.sync(Currency.wrap(address(sellToken)));

            if (payer == address(this)) {
                uint256 sellAmount = uint128(bytes16(data));
                data = data[16:];
                // TODO: bps
                sellToken.safeTransfer(_operator(), sellAmount);
            } else {
                assert(payer == address(0));
                // TODO: assert(bps == 0);

                ISignatureTransfer.PermitTransferFrom calldata permit;
                bool isForwarded;
                bytes calldata sig;
                assembly ("memory-safe") {
                    // this is super dirty, but it works because although `permit` is aliasing in the
                    // middle of `payer`, because `payer` is all zeroes, it's treated as padding for the
                    // first word of `permit`, which is the sell token
                    permit := sub(data.offset, 0x0c)
                    isForwarded := and(0x01, calldataload(add(0x55, data.offset)))

                    // `sig` is packed at the end of `data`, in "reverse ABIEncoded" fashion
                    let dataEnd := add(data.offset, data.length)
                    sig.offset := sub(dataEnd, 0x20)
                    sig.length := calldataload(sig.offset)
                    sig.offset := sub(sig.offset, sig.length)

                    // Remove `permit` and `isForwarded` from the front of `data`
                    data.offset := add(0x75, data.offset)
                    // Remove `sig` from the back of `data`
                    data.length := sub(sub(data.length, 0x95), sig.length)
                }

                // TODO: support partial fill
                sellAmount = _permitToSellAmount(permit)

                ISignatureTransfer.SignatureTransferDetails memory transferDetails =
                    ISignatureTransfer.SignatureTransferDetails({to: _operator(), requestedAmount: sellAmount});
                _transferFrom(permit, transferDetails, sig, isForwarded);
            }

            POOL_MANAGER.settle();
        }

        address recipient = address(uint160(bytes20(data)));
        data = data[20:];

        PoolKey memory key;
        IPoolManager.SwapParams memory params;
        bool zeroForOne;
        while (data.length > _HOP_LENGTH) {
            (zeroForOne, data) = _getPoolKey(key, data);
            params.zeroForOne = zeroForOne;
            int256 amountSpecified = -int256(sellAmount);
            params.amountSpecified = amountSpecified;
            // TODO: price limits
            params.sqrtPriceLimitX96 = zeroForOne ? 4295128740 : 1461446703485210103287273052203988822378723970341;

            bytes calldata hookData;
            (hookData, data) = _getHookData(data);

            BalanceDelta delta = _swap(key, params, hookData);
            sellAmount = uint256(int256((zeroForOne == amountSpecified < 0) ? delta.amount1() : delta.amount0()));
        }

        // sellAmount is now the actual buyAmount of buyToken
        if (sellAmount < minBuyAmount) {
            revert TooMuchSlippage(IERC20(Currency.unwrap(zeroForOne ? key.currency1 : key.currency0)) , minBuyAmount, buyAmount);
        }

        POOL_MANAGER.take(Current.wrap(address(buyToken)), recipient, sellAmount);

        return abi.encode(sellAmount);
    }

}

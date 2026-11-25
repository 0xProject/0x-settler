// SPDX-License-Identifier: MIT
pragma solidity =0.8.34;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SafeTransferLib} from "./vendor/SafeTransferLib.sol";

interface IPropAMM {
    function quote(IERC20 tokenIn, IERC20 tokenOut, uint256 amountIn) external returns (uint256 amountOut);
    function swap(
        IERC20 tokenIn,
        IERC20 tokenOut,
        uint256 amountIn,
        uint256 minAmountOut,
        address recipient,
        uint256 deadline
    ) external returns (uint256 amountOut);
}

/// @notice Stateless, immutable dispatcher across push-model `IPropAMM` venues.
/// Pulls `amountIn` directly from `msg.sender` to the chosen venue and reverts when no venue clears
/// `minOut` so Settler `SELECT` runs its fallback. When quoting backups, only the highest-quoted
/// venue is attempted and must deliver at least its quote.
contract PropAmmMux {
    using SafeTransferLib for IERC20;

    uint256 private constant _PRIMARY_GAS = 350_000;
    uint256 private constant _QUOTE_GAS = 0x249f0; // 150,000

    error NoLiveVenue();
    error InsufficientOutput(uint256 expected, uint256 actual);
    error OnlySelf();

    /// @notice If `primary` is non-zero, try it directly without quoting; on failure (or when
    /// `primary` is zero), quote `backups` and fill the highest live quote that meets `minOut`.
    /// `amountIn` sits at calldata offset `0x44` for Settler `BASIC`.
    function swap(
        IERC20 tokenIn,
        IERC20 tokenOut,
        uint256 amountIn,
        uint256 minOut,
        address recipient,
        uint256 deadline,
        IPropAMM primary,
        IPropAMM[] calldata backups
    ) external {
        if (address(primary) != address(0)) {
            try this._trySwap{gas: _PRIMARY_GAS}(
                primary, msg.sender, tokenIn, tokenOut, amountIn, minOut, recipient, deadline
            ) {
                return;
            } catch {}
        }

        (IPropAMM winner, uint256 bestQuote) = _pickBest(backups, tokenIn, tokenOut, amountIn, minOut);
        if (address(winner) == address(0)) revert NoLiveVenue();
        _fill(winner, msg.sender, tokenIn, tokenOut, amountIn, bestQuote, recipient, deadline);
    }

    function _trySwap(
        IPropAMM venue,
        address payer,
        IERC20 tokenIn,
        IERC20 tokenOut,
        uint256 amountIn,
        uint256 minOut,
        address recipient,
        uint256 deadline
    ) external {
        if (msg.sender != address(this)) revert OnlySelf();
        _fill(venue, payer, tokenIn, tokenOut, amountIn, minOut, recipient, deadline);
    }

    function _fill(
        IPropAMM venue,
        address payer,
        IERC20 tokenIn,
        IERC20 tokenOut,
        uint256 amountIn,
        uint256 minOut,
        address recipient,
        uint256 deadline
    ) private {
        uint256 beforeBal = tokenOut.fastBalanceOf(recipient);
        tokenIn.safeTransferFrom(payer, address(venue), amountIn);
        venue.swap(tokenIn, tokenOut, amountIn, minOut, recipient, deadline);
        uint256 amountOut = tokenOut.fastBalanceOf(recipient) - beforeBal;
        if (amountOut < minOut) revert InsufficientOutput(minOut, amountOut);
    }

    function _pickBest(
        IPropAMM[] calldata venues,
        IERC20 tokenIn,
        IERC20 tokenOut,
        uint256 amountIn,
        uint256 minOut
    ) private returns (IPropAMM winner, uint256 bestQuote) {
        for (uint256 i; i < venues.length; ++i) {
            (bool ok, uint256 q) = _tryQuote(venues[i], tokenIn, tokenOut, amountIn);
            if (ok && q >= minOut && q > bestQuote) {
                bestQuote = q;
                winner = venues[i];
            }
        }
    }

    function _tryQuote(IPropAMM venue, IERC20 tokenIn, IERC20 tokenOut, uint256 amountIn)
        private
        returns (bool ok, uint256 amountOut)
    {
        // Bounded low-level `call`: accepts a successful call returning at least 32 bytes, avoids
        // ABI-decode reverts on malformed data, and caps gas so one venue cannot starve backups.
        // Equivalent to:
        //   try venue.quote{gas: _QUOTE_GAS}(tokenIn, tokenOut, amountIn) returns (uint256 out) {
        //       return (true, out);
        //   } catch { return (false, 0); }
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(ptr, 0xb646638400000000000000000000000000000000000000000000000000000000)
            mstore(add(0x04, ptr), tokenIn)
            mstore(add(0x24, ptr), tokenOut)
            mstore(add(0x44, ptr), amountIn)
            ok := call(_QUOTE_GAS, venue, 0x00, ptr, 0x64, 0x00, 0x20)
            if and(ok, lt(0x1f, returndatasize())) {
                amountOut := mload(0x00)
            }
        }
    }
}

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

/// @notice A failed primary fill rolls back its token transfer before backups are quoted.
contract PropAmmMux {
    using SafeTransferLib for IERC20;

    uint256 private constant _PRIMARY_GAS = 350_000;
    uint256 private constant _QUOTE_GAS = 150_000;

    error NoLiveVenue();
    error InsufficientOutput(uint256 expected, uint256 actual);
    error OnlySelf();

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
            bytes memory data = abi.encodeCall(
                this._trySwap, (primary, msg.sender, tokenIn, tokenOut, amountIn, minOut, recipient, deadline)
            );
            bool filled;
            // Cap gas and copy zero return bytes: `filled = address(this).call{gas: _PRIMARY_GAS}(data)`.
            assembly ("memory-safe") {
                filled := call(_PRIMARY_GAS, address(), 0x00, add(0x20, data), mload(data), 0x00, 0x00)
            }
            if (filled) return;
        }

        IPropAMM winner;
        uint256 bestQuote;
        bytes memory query = abi.encodeCall(IPropAMM.quote, (tokenIn, tokenOut, amountIn));
        for (uint256 i; i < backups.length; ++i) {
            IPropAMM venue = backups[i];
            uint256 q;
            // Cap gas and copy at most one word: `q = ok && ret.length >= 32 ? abi.decode(ret, (uint256)) : 0`.
            assembly ("memory-safe") {
                if call(_QUOTE_GAS, venue, 0x00, add(0x20, query), mload(query), 0x00, 0x20) {
                    if lt(0x1f, returndatasize()) { q := mload(0x00) }
                }
            }
            if (q > bestQuote) {
                bestQuote = q;
                winner = venue;
            }
        }
        if (address(winner) == address(0) || bestQuote < minOut) revert NoLiveVenue();
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
}

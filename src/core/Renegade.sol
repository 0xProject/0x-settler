// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SettlerSwapAbstract} from "../SettlerAbstract.sol";
import {revertTooMuchSlippage} from "./SettlerErrors.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";

abstract contract Renegade is SettlerSwapAbstract {
    using SafeTransferLib for IERC20;

    /*
     * Memory layout of `data` (the args to `sponsorExternalMatch`, sans the
     * 4-byte selector). The first 32 bytes are the bytes-length word; the
     * payload begins at `data + 0x20`. Offsets below are relative to `data`
     * itself, matching the `mload(add(data, OFFSET))` reads in this file.
     *
     *   sponsorExternalMatch(
     *     0x20   uint256   sellTokenAmt
     *     0x40   address   recipient
     *     0x60   address   internalPartyInputToken    \
     *     0x80   address   internalPartyOutputToken    | BoundedMatchResult
     *     0xa0   uint256   price.repr (FixedPoint)     | (inlined static struct,
     *     0xc0   uint256   minInternalPartyAmountIn    |  six 32-byte words)
     *     0xe0   uint256   maxInternalPartyAmountIn    |
     *     0x100  uint256   blockDeadline              /
     *     0x120  uint256   <offset>  SettlementBundle: (bool isFirstFill, uint8 bundleType, bytes data)
     *     0x140  uint256   <offset>  GasSponsorOptions: (address refundAddress, bool refundNativeEth, uint256 refundAmount, uint256 nonce, bytes signature)
     *   )
     */
    uint32 internal constant RENEGADE_SELECTOR = uint32(
        bytes4(
            keccak256(
                "sponsorExternalMatch(uint256,address,(address,address,(uint256),uint256,uint256,uint256),(bool,uint8,bytes),(address,bool,uint256,uint256,bytes))"
            )
        )
    );

    /// @notice The expected `GasSponsorV2` proxy address for the current chain.
    /// @dev Adding a new chain requires a source change + redeploy of this contract.
    function _renegadeGasSponsorV2() internal view returns (address) {
        uint256 chainId = block.chainid;
        if (chainId == 42161) return 0xcE7a8D45daa9a5B29f6d255552F577d53fF9EBcf; // Arbitrum One
        if (chainId == 8453) return 0xD9E0507D706408D0f14E22e50880189Fd915be80; // Base mainnet
        revert("Renegade: unsupported chain");
    }

    /*
     * @param target The `GasSponsorV2` contract address.
     * @param sellToken The token that the taker is selling (the sell-token).
     * @param data The ABI-encoded (sans 4-byte selector) calldata to
     *             `sponsorExternalMatch()`
     * @param minBuyAmt The minimum amount of the buy-token the taker must receive.
     */
    function sellToRenegade(address target, IERC20 sellToken, bytes memory data, uint256 minBuyAmt)
        internal
        returns (uint256 buyAmt)
    {
        // Extract the recipient from `data` and require that it resolves to address(this).
        address recipient;
        assembly ("memory-safe") {
            recipient := mload(add(data, 0x40))
        }
        require((recipient == address(0)) || (recipient == address(this)), "Renegade: bad recipient");

        // Extract buyToken and the expected sellToken from `data`.
        IERC20 buyToken;
        IERC20 internalPartyOutputToken;
        assembly ("memory-safe") {
            buyToken := mload(add(data, 0x60))
            internalPartyOutputToken := mload(add(data, 0x80))
        }
        require(sellToken == internalPartyOutputToken, "Renegade: bad sellToken");

        // Extract `minInternalPartyAmountIn` and `maxInternalPartyAmountIn` from `data`
        uint256 minInternalPartyAmountIn;
        uint256 maxInternalPartyAmountIn;
        assembly ("memory-safe") {
            minInternalPartyAmountIn := mload(add(data, 0xc0))
            maxInternalPartyAmountIn := mload(add(data, 0xe0))
        }

        // We need to look up the sellToken balance here because previous hops
        // may have already swapped it, so it may be different than the amount
        // that the user expects.
        uint256 newSellAmt = sellToken.fastBalanceOf(address(this));

        // Extract price from `data`.
        uint256 priceRepr;
        assembly ("memory-safe") {
            priceRepr := mload(add(data, 0xa0))
        }

        // newBuyAmt = floor(newSellAmt / price), matching
        // FixedPointLib.divIntegerByFixedPoint.
        uint256 newBuyAmt = (newSellAmt << 63) / priceRepr;

        // Check newBuyAmt
        if (newBuyAmt < minBuyAmt) revertTooMuchSlippage(buyToken, minBuyAmt, newBuyAmt);
        require(newBuyAmt >= minInternalPartyAmountIn, "Renegade: newBuyAmt < minInternalPartyAmountIn");
        require(newBuyAmt <= maxInternalPartyAmountIn, "Renegade: newBuyAmt > maxInternalPartyAmountIn");

        require(target == _renegadeGasSponsorV2(), "Renegade: bad target");

        // Snapshot the buyToken balance before the call so we can measure the
        // actual amount transferred after.
        uint256 buyTokenBalanceBefore = buyToken.fastBalanceOf(address(this));

        // Allow the sellToken contract to move newSellAmt tokens from this contract.
        sellToken.safeApproveIfBelow(address(target), newSellAmt);

        uint32 sel = RENEGADE_SELECTOR;

        assembly ("memory-safe") {
            // Override sellTokenAmt in data (at position 0x20) with newSellAmt.
            mstore(add(data, 0x20), newSellAmt)

            // data[0x00..0x20) holds the length, data[0x20..) is the payload.
            // Stash the length and overwrite the length word with the 32-byte
            // selector. The 4-byte selector occupies the low 4 bytes of that
            // word, so the on-the-wire calldata [selector | payload] begins at
            // data + 0x1c (0x20 - 4).
            let len := mload(data)
            mstore(data, sel)

            // Invoke sponsorExternalMatch():
            //   in     = data + 0x1c        (start of [selector | payload])
            //   insize = 4 + len            (4-byte selector + len-byte payload)
            //   out/outsize = 0             (returndata not consumed on success;
            //                                on revert we copy returndata directly
            //                                from the precompile buffer and bubble it)
            if iszero(call(gas(), target, 0, add(0x1c, data), add(0x04, len), 0x00, 0x00)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }

            // Restore the length word clobbered with the selector. Required to
            // (a) keep `data` a valid `bytes memory` for any subsequent reads, and
            // (b) honor the memory-safe assembly contract, which forbids leaving
            // compiler-managed slots in a corrupted state on exit.
            mstore(data, len)
        }

        // Check the balance delta.
        buyAmt = buyToken.fastBalanceOf(address(this)) - buyTokenBalanceBefore;
        if (buyAmt < minBuyAmt) revertTooMuchSlippage(buyToken, minBuyAmt, buyAmt);
    }
}

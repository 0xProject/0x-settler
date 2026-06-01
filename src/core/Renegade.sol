// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SettlerSwapAbstract} from "../SettlerAbstract.sol";
import {revertInvalidRenegadeData, revertInvalidTarget, revertTooMuchSlippage} from "./SettlerErrors.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";

abstract contract Renegade is SettlerSwapAbstract {
    using SafeTransferLib for IERC20;
    using UnsafeMath for uint256;

    /*
     * Memory layout of `data` (the args to `sponsorExternalMatch`, sans the
     * 4-byte selector). The first 32 bytes are the bytes-length word; the
     * payload begins at `data + 0x20`. Offsets below are relative to `data`
     * itself, matching the `mload(add(OFFSET, data))` reads in this file.
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
    uint32 private constant RENEGADE_SELECTOR = 0x54ea46d4;

    /// @notice The expected `GasSponsorV2` proxy address for the current chain.
    /// @dev Adding a new chain requires a source change + redeploy of this contract.
    function _renegadeGasSponsorV2() internal pure virtual returns (address);

    function sellToRenegade(address target, IERC20 sellToken, bytes memory data, uint256 minBuyAmt)
        internal
        returns (uint256 buyAmt)
    {
        address recipient;
        IERC20 buyToken;
        IERC20 internalPartyOutputToken;
        uint256 minInternalPartyAmountIn;
        uint256 maxInternalPartyAmountIn;
        uint256 priceRepr;
        assembly ("memory-safe") {
            recipient := mload(add(0x40, data))
            buyToken := mload(add(0x60, data))
            internalPartyOutputToken := mload(add(0x80, data))
            priceRepr := mload(add(0xa0, data))
            minInternalPartyAmountIn := mload(add(0xc0, data))
            maxInternalPartyAmountIn := mload(add(0xe0, data))
        }
        if ((recipient != address(0)) && (recipient != address(this))) revertInvalidRenegadeData();
        if (sellToken != internalPartyOutputToken) revertInvalidRenegadeData();
        if (priceRepr == 0) revertInvalidRenegadeData();

        uint256 newSellAmt = sellToken.fastBalanceOf(address(this));

        // newBuyAmt = floor(newSellAmt / price), matching
        // FixedPointLib.divIntegerByFixedPoint.
        uint256 newBuyAmt = (newSellAmt << 63).unsafeDiv(priceRepr);

        if (newBuyAmt < minBuyAmt) revertTooMuchSlippage(buyToken, minBuyAmt, newBuyAmt);
        if (newBuyAmt < minInternalPartyAmountIn) revertInvalidRenegadeData();
        if (newBuyAmt > maxInternalPartyAmountIn) revertInvalidRenegadeData();

        if (target != _renegadeGasSponsorV2()) revertInvalidTarget();

        uint256 buyTokenBalanceBefore = buyToken.fastBalanceOf(address(this));
        sellToken.safeApproveIfBelow(address(target), newSellAmt);

        assembly ("memory-safe") {
            // Override sellTokenAmt in data (at position 0x20) with newSellAmt.
            mstore(add(0x20, data), newSellAmt)

            // Stash the length and overwrite its slot with the selector; calldata
            // starts at data + 0x1c so the call sees [selector | payload].
            let len := mload(data)
            mstore(data, RENEGADE_SELECTOR)

            if iszero(call(gas(), target, 0, add(0x1c, data), add(0x04, len), 0x00, 0x00)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }

            // Restore the clobbered length word before leaving memory-safe assembly.
            mstore(data, len)
        }

        buyAmt = buyToken.fastBalanceOf(address(this)) - buyTokenBalanceBefore;
        if (buyAmt < minBuyAmt) revertTooMuchSlippage(buyToken, minBuyAmt, buyAmt);
    }
}

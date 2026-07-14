// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SettlerSwapAbstract} from "../SettlerAbstract.sol";
import {revertInvalidRenegadeData, revertTooMuchSlippage} from "./SettlerErrors.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";

abstract contract Renegade is SettlerSwapAbstract {
    using SafeTransferLib for IERC20;

    // selector for `sponsorExternalMatch(uint256,address,(address,address,(uint256),uint256,uint256,uint256),(bool,uint8,bytes),(address,bool,uint256,uint256,bytes))`
    // `data` excludes the selector and the first four ABI words (amount, recipient, buy token, sell token).
    uint32 private constant RENEGADE_SELECTOR = 0x54ea46d4;

    /// @dev Chain-specific `GasSponsorV2` proxy. Adding a chain requires source change + redeploy.
    function _renegadeGasSponsorV2() internal pure virtual returns (address);

    /// @dev `maxRefundAmount` is the signed requested refund. Subtracting included refunds conservatively
    /// undercounts trade proceeds when sponsorship is skipped or underfunded.
    function sellToRenegade(
        address recipient,
        IERC20 sellToken,
        IERC20 buyToken,
        uint256 maxSellAmount,
        bool refundNativeEth,
        uint256 maxRefundAmount,
        bytes memory data,
        uint256 minBuyAmount
    ) internal {
        if (data.length < 0x120) revertInvalidRenegadeData(); // remaining static head plus required options fields

        uint256 sellAmt = sellToken.fastBalanceOf(address(this));
        if (sellAmt > maxSellAmount) sellAmt = maxSellAmount;
        address target = _renegadeGasSponsorV2();
        sellToken.safeApproveIfBelow(target, sellAmt);

        uint256 buyAmt;
        // Assembly avoids decoding and re-encoding the opaque signed structs in `data`.
        // Equivalent Solidity pseudocode:
        // fullData = bytes.concat(abi.encode(sellAmt, recipient, buyToken, sellToken), data);
        // (amountIn, requestRecipient, matchResult, bundle, options) = abi.decode(fullData, (...));
        // matchResult.internalPartyInputToken = buyToken;
        // matchResult.internalPartyOutputToken = sellToken;
        // options.refundNativeEth = refundNativeEth;
        // options.refundAmount = maxRefundAmount;
        // buyAmt = GasSponsorV2(target).sponsorExternalMatch(
        //     sellAmt, recipient, matchResult, bundle, options
        // );
        assembly ("memory-safe") {
            let len := mload(data)
            let fullLen := add(0x80, len)
            let optionsOffset := mload(add(0xc0, data))
            if or(and(optionsOffset, 0x1f), or(lt(optionsOffset, 0x140), gt(optionsOffset, sub(fullLen, 0x60)))) {
                mstore(0x00, 0xaa81f37c) // selector for `InvalidRenegadeData()`
                revert(0x1c, 0x04)
            }

            // Reconstruct the sponsor calldata from the typed prefix and opaque suffix.
            let callData := mload(0x40)
            mstore(0x40, and(add(add(0xbf, callData), len), not(0x1f)))
            mstore(callData, RENEGADE_SELECTOR)
            mstore(add(0x20, callData), sellAmt)
            mstore(add(0x40, callData), recipient)
            mstore(add(0x60, callData), buyToken)
            mstore(add(0x80, callData), sellToken)
            mcopy(add(0xa0, callData), add(0x20, data), len)
            mstore(add(0x40, add(callData, optionsOffset)), refundNativeEth)
            mstore(add(0x60, add(callData, optionsOffset)), maxRefundAmount)

            if iszero(call(gas(), target, 0x00, add(0x1c, callData), add(0x84, len), 0x00, 0x20)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }

            if lt(returndatasize(), 0x20) {
                mstore(0x00, 0xaa81f37c) // selector for `InvalidRenegadeData()`
                revert(0x1c, 0x04)
            }
            buyAmt := mload(0x00)
        }

        if (!refundNativeEth || buyToken == ETH_ADDRESS) {
            unchecked {
                if (buyAmt > maxRefundAmount) buyAmt -= maxRefundAmount;
                else buyAmt = 0;
            }
        }
        if (buyAmt < minBuyAmount) revertTooMuchSlippage(buyToken, minBuyAmount, buyAmt);
    }
}

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SettlerSwapAbstract} from "../SettlerAbstract.sol";
import {revertInvalidRenegadeData, revertTooMuchSlippage} from "./SettlerErrors.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";

abstract contract Renegade is SettlerSwapAbstract {
    using SafeTransferLib for IERC20;

    // selector for `sponsorExternalMatch(uint256,address,(address,address,(uint256),uint256,uint256,uint256),(bool,uint8,bytes),(address,bool,uint256,uint256,bytes))`
    // `data` excludes the selector. Its static head starts at `data + 0x20`:
    // 0x20 amountIn, 0x40 recipient, 0x60 external-party buy token, 0x80 external-party sell token.
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
        if (data.length < 0x1a0) revertInvalidRenegadeData(); // static head plus the required options fields

        uint256 sellAmt = sellToken.fastBalanceOf(address(this));
        if (sellAmt > maxSellAmount) sellAmt = maxSellAmount;
        address target = _renegadeGasSponsorV2();
        sellToken.safeApproveIfBelow(target, sellAmt);

        uint256 buyAmt;
        // Equivalent Solidity: validate and patch the ABI payload, call the sponsor, bubble failures,
        // and decode its uint256 return. Assembly avoids re-encoding the signed dynamic payload.
        assembly ("memory-safe") {
            let len := mload(data)
            let optionsOffset := mload(add(0x140, data))
            if or(and(optionsOffset, 0x1f), or(lt(optionsOffset, 0x140), gt(optionsOffset, sub(len, 0x60)))) {
                mstore(0x00, 0xaa81f37c) // selector for `InvalidRenegadeData()`
                revert(0x1c, 0x04)
            }

            // Patch caller-malleable args and bind typed fields into proof-authenticated data.
            mstore(add(0x20, data), sellAmt)
            mstore(add(0x40, data), recipient)
            mstore(add(0x60, data), buyToken)
            mstore(add(0x80, data), sellToken)
            mstore(add(0x40, add(data, optionsOffset)), refundNativeEth)
            mstore(add(0x60, add(data, optionsOffset)), maxRefundAmount)

            // Stash the length and overwrite its slot with the selector; calldata starts at data + 0x1c.
            mstore(data, RENEGADE_SELECTOR)

            if iszero(call(gas(), target, 0x00, add(0x1c, data), add(0x04, len), 0x00, 0x20)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }

            // Restore the clobbered length word before leaving memory-safe assembly.
            mstore(data, len)

            if lt(returndatasize(), 0x20) {
                mstore(0x00, 0xaa81f37c) // selector for `InvalidRenegadeData()`
                revert(0x1c, 0x04)
            }
            buyAmt := mload(0x00)
        }

        if (!refundNativeEth || buyToken == ETH_ADDRESS) {
            if (buyAmt > maxRefundAmount) buyAmt -= maxRefundAmount;
            else buyAmt = 0;
        }
        if (buyAmt < minBuyAmount) revertTooMuchSlippage(buyToken, minBuyAmount, buyAmt);
    }
}

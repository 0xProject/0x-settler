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

    /// @dev Checks the amount Renegade returns for the external party. Central slippage still backstops
    /// settler-custody routes.
    function sellToRenegade(
        address recipient,
        IERC20 sellToken,
        uint256 maxSellAmount,
        bytes memory data,
        uint256 minBuyAmount
    ) internal {
        if (data.length < 0x140) revertInvalidRenegadeData(); // full static head: 8 words + 2 tail offsets

        uint256 sellAmt = sellToken.fastBalanceOf(address(this));
        if (sellAmt > maxSellAmount) sellAmt = maxSellAmount;
        address target = _renegadeGasSponsorV2();
        sellToken.safeApproveIfBelow(target, sellAmt);

        IERC20 buyToken;
        uint256 buyAmt;
        assembly ("memory-safe") {
            // Patch caller-malleable args and force the approved sell token into the proof-bound match.
            mstore(add(0x20, data), sellAmt)
            mstore(add(0x40, data), recipient)
            buyToken := mload(add(0x60, data))
            mstore(add(0x80, data), sellToken)

            // Stash the length and overwrite its slot with the selector; calldata starts at data + 0x1c.
            let len := mload(data)
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

        if (buyAmt < minBuyAmount) revertTooMuchSlippage(buyToken, minBuyAmount, buyAmt);
    }
}

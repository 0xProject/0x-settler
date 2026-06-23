// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SettlerSwapAbstract} from "../SettlerAbstract.sol";
import {revertInvalidRenegadeData} from "./SettlerErrors.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";

abstract contract Renegade is SettlerSwapAbstract {
    using SafeTransferLib for IERC20;

    // `data` is the args to `sponsorExternalMatch` minus the 4-byte selector; its payload begins at
    // `data + 0x20`. The head is static (`BoundedMatchResult` is inlined), so we index fixed offsets:
    // 0x20 externalPartyAmountIn, 0x40 recipient, 0x80 internalPartyOutputToken.
    uint32 private constant RENEGADE_SELECTOR = 0x54ea46d4;

    /// @notice The expected `GasSponsorV2` proxy address for the current chain.
    /// @dev Adding a new chain requires a source change + redeploy of this contract.
    function _renegadeGasSponsorV2() internal pure virtual returns (address);

    /// @dev Slippage is enforced centrally by `_checkSlippageAndTransfer`; this action performs no
    /// slippage check of its own. The match price/bounds/deadline are validated by the GasSponsor.
    function sellToRenegade(IERC20 sellToken, bytes memory data) internal {
        if (data.length < 0x80) revertInvalidRenegadeData();

        IERC20 internalPartyOutputToken;
        assembly ("memory-safe") {
            internalPartyOutputToken := mload(add(0x80, data))
        }
        // The sponsor pulls `internalPartyOutputToken`; require it to be the token we approve so a
        // residual max approval to the sponsor can't be used to pull a different token.
        if (sellToken != internalPartyOutputToken) revertInvalidRenegadeData();

        uint256 newSellAmt = sellToken.fastBalanceOf(address(this));
        address target = _renegadeGasSponsorV2();
        sellToken.safeApproveIfBelow(target, newSellAmt);

        assembly ("memory-safe") {
            // Override externalPartyAmountIn with our balance and force recipient to this settler, so the
            // match output lands in our custody for the final slippage check.
            mstore(add(0x20, data), newSellAmt)
            mstore(add(0x40, data), address())

            // Stash the length and overwrite its slot with the selector; calldata starts at data + 0x1c.
            let len := mload(data)
            mstore(data, RENEGADE_SELECTOR)

            if iszero(call(gas(), target, 0x00, add(0x1c, data), add(0x04, len), 0x00, 0x00)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }

            // Restore the clobbered length word before leaving memory-safe assembly.
            mstore(data, len)
        }
    }
}

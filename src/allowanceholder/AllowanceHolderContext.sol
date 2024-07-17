// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Context} from "../Context.sol";
import {IAllowanceHolder} from "./IAllowanceHolder.sol";

abstract contract AllowanceHolderContext is Context {
    IAllowanceHolder internal constant _ALLOWANCE_HOLDER = IAllowanceHolder(0x0000000000005E88410CcDFaDe4a5EfaE4b49562);

    function _isForwarded() internal view virtual override returns (bool) {
        return super._isForwarded() || super._msgSender() == address(_ALLOWANCE_HOLDER);
    }

    function _msgSender() internal view virtual override returns (address sender) {
        sender = super._msgSender();
        if (sender == address(_ALLOWANCE_HOLDER)) {
            // ERC-2771 like usage where the _trusted_ `AllowanceHolder` has appended the appropriate
            // msg.sender to the msg data
            assembly ("memory-safe") {
                sender := shr(0x60, calldataload(sub(calldatasize(), 0x14)))
            }
        }
    }

    // this is here to avoid foot-guns and make it very explicit that we intend
    // to pass the confused deputy check in AllowanceHolder
    function balanceOf(address) external pure {
        assembly ("memory-safe") {
            mstore8(0x00, 0x00)
            revert(0x00, 0x01)
        }
    }
}

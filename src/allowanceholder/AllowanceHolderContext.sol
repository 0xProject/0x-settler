// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Context} from "../Context.sol";
import {IAllowanceHolder, ALLOWANCE_HOLDER} from "./IAllowanceHolder.sol";

abstract contract AllowanceHolderContext is Context {
    function _isForwarded() internal view virtual override returns (bool) {
        return super._isForwarded() || super._msgSender() == address(ALLOWANCE_HOLDER);
    }

    function _msgData() internal view virtual override returns (bytes calldata) {
        if (super._msgSender() == address(ALLOWANCE_HOLDER)) {
            return msg.data[:msg.data.length - 20];
        } else {
            return msg.data;
        }
    }

    function _msgSender() internal view virtual override returns (address sender) {
        sender = super._msgSender();
        if (sender == address(ALLOWANCE_HOLDER)) {
            // ERC-2771 like usage where the _trusted_ `AllowanceHolder` has appended the appropriate
            // msg.sender to the msg data
            bytes calldata data = super._msgData();
            assembly ("memory-safe") {
                sender := shr(0x60, calldataload(add(data.offset, sub(data.length, 0x14))))
            }
        }
    }

    // this is here to avoid foot-guns and make it very explicit that we intend
    // to pass the confused deputy check in AllowanceHolder
    function balanceOf(address) external pure {
        assembly ("memory-safe") {
            mstore8(0x00, 0x00)
            return(0x00, 0x01)
        }
    }
}

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {Context} from "./Context.sol";
import {IAllowanceHolder} from "./IAllowanceHolder.sol";

abstract contract AllowanceHolderContext is Context {
    IAllowanceHolder public immutable allowanceHolder;

    constructor(address _allowanceHolder) {
        allowanceHolder = IAllowanceHolder(_allowanceHolder);
    }

    function _isForwarded() internal view virtual override returns (bool) {
        return msg.sender == address(allowanceHolder) || super._isForwarded();
    }

    function _msgSender() internal view virtual override returns (address sender) {
        if (msg.sender == address(allowanceHolder)) {
            // EIp-2771 like usage where the _trusted_ `AllowanceHolder` has appended the appropriate
            // msg.sender to the msg data
            assembly {
                sender := shr(96, calldataload(sub(calldatasize(), 20)))
            }
        } else {
            sender = super._msgSender();
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

    // We're definitely not an ERC20. Understand!?!?
    function transfer(address, uint256) external pure {
        assembly ("memory-safe") {
            mstore8(0x00, 0x00)
            revert(0x00, 0x01)
        }
    }

    function transferFrom(address, address, uint256) external pure {
        assembly ("memory-safe") {
            mstore8(0x00, 0x00)
            revert(0x00, 0x01)
        }
    }
}

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {Context} from "../Context.sol";
import {IAllowanceHolder} from "./IAllowanceHolder.sol";

abstract contract AllowanceHolderContext is Context {
    IAllowanceHolder public immutable allowanceHolder;

    constructor(address _allowanceHolder) {
        allowanceHolder = IAllowanceHolder(_allowanceHolder);
    }

    function _isForwarded() internal view virtual override returns (bool) {
        return super._isForwarded() || super._msgSender() == address(allowanceHolder);
    }

    function _msgSender() internal view virtual override returns (address sender) {
        sender = super._msgSender();
        if (sender == address(allowanceHolder)) {
            // ERC-2771 like usage where the _trusted_ `AllowanceHolder` has appended the appropriate
            // msg.sender to the msg data
            assembly ("memory-safe") {
                sender := shr(0x60, calldataload(sub(calldatasize(), 0x14)))
            }
        }
    }

    function _encodeDelegateCall(bytes memory callData) internal view virtual override returns (bytes memory) {
        callData = super._encodeDelegateCall(callData);
        if (super._msgSender() == address(allowanceHolder)) {
            address forwardedSender;
            assembly ("memory-safe") {
                forwardedSender := shr(0x60, calldataload(sub(calldatasize(), 0x14)))
            }
            return abi.encodePacked(callData, forwardedSender);
        }
        return callData;
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

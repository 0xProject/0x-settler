// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {Context} from "./Context.sol";
import {AllowanceHolder} from "./AllowanceHolder.sol";

abstract contract AllowanceHolderContext is Context {
    AllowanceHolder public immutable allowanceHolder;

    constructor(address _allowanceHolder) {
        allowanceHolder = AllowanceHolder(_allowanceHolder);
    }

    function _isForwarded() internal view virtual override returns (bool) {
        return msg.sender == address(allowanceHolder) || super._isForwarded();
    }

    function _msgSender() internal view virtual override returns (address sender) {
        if (msg.sender == address(allowanceHolder)) {
            sender = tx.origin;
        } else {
            sender = super._msgSender();
        }
    }
}

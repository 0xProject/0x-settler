// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {Context} from "./Context.sol";

abstract contract ERC2771Context is Context {
    address public immutable trustedForwarder;

    constructor(address _trustedForwarder) {
        trustedForwarder = _trustedForwarder;
    }

    function isTrustedForwarder(address forwarder) public view virtual returns (bool) {
        return forwarder == trustedForwarder;
    }

    function _isERC2771Forwarded() internal view virtual returns (bool) {
        return isTrustedForwarder(msg.sender) && msg.data.length >= 20;
    }

    function _isForwarded() internal view virtual override returns (bool) {
        return _isERC2771Forwarded() || super._isForwarded();
    }

    function _msgSender() internal view virtual override returns (address sender) {
        if (_isERC2771Forwarded()) {
            assembly ("memory-safe") {
                sender := shr(96, calldataload(sub(calldatasize(), 20)))
            }
        } else {
            sender = super._msgSender();
        }
    }

    function _msgData() internal view virtual override returns (bytes calldata) {
        return _isERC2771Forwarded() ? msg.data[:msg.data.length - 20] : super._msgData();
    }
}

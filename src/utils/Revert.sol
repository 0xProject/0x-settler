// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

library Revert {
    function _revert(bytes memory reason) internal pure {
        assembly ("memory-safe") {
            revert(add(reason, 0x20), mload(reason))
        }
    }

    function maybeRevert(bool success, bytes memory reason) internal pure {
        if (!success) {
            _revert(reason);
        }
    }
}

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

library LibBytes {
    using LibBytes for bytes;

    function popSelector(bytes memory data) internal pure returns (bytes memory) {
        return sliceDestructive(data, 4, data.length);
    }

    function sliceDestructive(bytes memory b, uint256 from, uint256 to) internal pure returns (bytes memory result) {
        // Create a new bytes structure around [from, to) in-place.
        assembly {
            result := add(b, from)
            mstore(result, sub(to, from))
        }
        return result;
    }
}

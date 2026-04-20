// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

library AltItoA {
    function altItoa(uint256 value) internal pure returns (string memory) {
        // From OpenZeppelin Contracts v4.7.0 (utils/Strings.sol) - MIT license
        // Inspired by OraclizeAPI's implementation - MIT licence
        if (value == 0) {
            return "0";
        }
        uint256 temp = value;
        uint256 digits;
        while (temp != 0) {
            digits++;
            temp /= 10;
        }
        bytes memory buffer = new bytes(digits);
        while (value != 0) {
            digits -= 1;
            buffer[digits] = bytes1(uint8(48 + uint256(value % 10)));
            value /= 10;
        }
        return string(buffer);
    }

    function altItoa(int256 value) internal pure returns (string memory) {
        if (value < 0) {
            return string.concat("-", altItoa(uint256(-value)));
        } else {
            return altItoa(uint256(value));
        }
    }
}

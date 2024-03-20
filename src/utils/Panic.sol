// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

library Panic {
    function panic(uint256 code) internal pure {
        assembly ("memory-safe") {
            mstore(0x00, 0x4e487b71) // selector for `Panic(uint256)`
            mstore(0x20, code)
            revert(0x1c, 0x24)
        }
    }

    // https://docs.soliditylang.org/en/latest/control-structures.html#panic-via-assert-and-error-via-require
    uint8 internal constant GENERIC = 0x00;
    uint8 internal constant ASSERT_FAIL = 0x01;
    uint8 internal constant ARITHMETIC_OVERFLOW = 0x11;
    uint8 internal constant DIVISION_BY_ZERO = 0x12;
    uint8 internal constant ENUM_CAST = 0x21;
    uint8 internal constant CORRUPT_STORAGE_ARRAY = 0x22;
    uint8 internal constant POP_EMPTY_ARRAY = 0x31;
    uint8 internal constant ARRAY_OUT_OF_BOUNDS = 0x32;
    uint8 internal constant OUT_OF_MEMORY = 0x41;
    uint8 internal constant ZERO_FUNCTION_POINTER = 0x51;
}

// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.25;

import {TransientStorageBase} from "src/allowanceholder/TransientStorageBase.sol";
import {TransientStorageLayout} from "src/allowanceholder/TransientStorageLayout.sol";
import {TransientStorage} from "src/allowanceholder/TransientStorage.sol";

contract TransientStorageHarness is TransientStorageLayout, TransientStorage {

    // Round-trip: tstore(s, v) then tload(s) must return v.
    function setThenGet(bytes32 s, uint256 v) external returns (uint256) {
        _set(TransientStorageBase.TSlot.wrap(s), v);
        return _get(TransientStorageBase.TSlot.wrap(s));
    }

    // Slot independence: writing a DIFFERENT slot s2 must not disturb slot s1.
    function setTwoThenGet(bytes32 s1, uint256 v1, bytes32 s2, uint256 v2)
        external
        returns (uint256)
    {
        _set(TransientStorageBase.TSlot.wrap(s1), v1);
        _set(TransientStorageBase.TSlot.wrap(s2), v2);
        return _get(TransientStorageBase.TSlot.wrap(s1));
    }


    // Overwrite: tstore(s, v1) then tstore(s, v2) then tload(s) must return v2.
    function setOverwriteThenGet(bytes32 s, uint256 v1, uint256 v2) external returns (uint256) {
        _set(TransientStorageBase.TSlot.wrap(s), v1);
        _set(TransientStorageBase.TSlot.wrap(s), v2);
        return _get(TransientStorageBase.TSlot.wrap(s));
    }

    // REAL production slot — calls the unsummarized assembly _ephemeralAllowance.
    function ephemeralSlotHarness(address operator, address owner, address token)
        external
        pure
        returns (bytes32)
    {
        return TransientStorageBase.TSlot.unwrap(_ephemeralAllowance(operator, owner, token));
    }

    // VERBATIM transcription of the production assembly (identical construction).
    function transcribedSlotHarness(address operator, address owner, address token)
        external
        pure
        returns (bytes32 r)
    {
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(0x28, token)
            mstore(0x14, owner)
            mstore(0x00, operator)
            r := keccak256(0x0c, 0x3c)
            mstore(0x40, ptr)
        }
    }

    // Production keccak PREIMAGE as two word-aligned bytes32 words (the exact 60
    // bytes the production keccak256(0x0c, 0x3c) consumes), read instead of hashed.
    function prodPreimageWords(address operator, address owner, address token)
        external
        pure
        returns (bytes32 w0, bytes32 w1)
    {
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(0x28, token)
            mstore(0x14, owner)
            mstore(0x00, operator)
            w0 := mload(0x0c) // preimage[0:32)
            w1 := shr(32, mload(0x2c)) // preimage[32:60) right-aligned (drop 4 trailing bytes)
            mstore(0x40, ptr) // restore FMP
        }
    }

    // Documented-formula PREIMAGE (abi.encodePacked(operator, owner, token)),
    // reconstructed arithmetically to match prodPreimageWords' word layout.
    function refPreimageWords(address operator, address owner, address token)
        external
        pure
        returns (bytes32 w0, bytes32 w1)
    {
        uint256 op = uint256(uint160(operator));
        uint256 ow = uint256(uint160(owner));
        uint256 tk = uint256(uint160(token));

        w0 = bytes32((op << 96) | (ow >> 64));
        w1 = bytes32(((ow & 0xFFFFFFFFFFFFFFFF) << 160) | tk);
    }

    function ephemeralAllowanceHarness(address operator, address owner, address token) external pure returns (bytes32) {
        return TSlot.unwrap(_ephemeralAllowance(operator, owner, token));
    }
}

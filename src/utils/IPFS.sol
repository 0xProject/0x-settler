// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Panic} from "./Panic.sol";

library IPFS {
    /// @return r SHA256(Protobuf({1: Protobuf({1: 2, 2: contentString, 3: contentString.length})}))
    /// @param contentString File contents to be encoded and hashed
    /// @dev if `contentString` is empty, field 2 is omitted, but field 3 is retained as zero
    /// @dev if `contentString` is longer than 256kiB, it exceeds an IPFS chunk and cannot be handled by this function (reverts)
    function dagPbUnixFsHash(string memory contentString) internal view returns (bytes32 r) {
        unchecked {
            uint256 contentLength = bytes(contentString).length;
            if (contentLength >= 0x40001) {
                Panic.panic(Panic.OUT_OF_MEMORY);
            }
            bytes memory len = _protobufVarint(contentLength);
            bytes memory len2 = _protobufVarint(contentLength == 0 ? 4 : contentLength + 4 + 2 * len.length);
            assembly ("memory-safe") {
                let ptr := mload(0x40)
                let dst := ptr
                mstore8(ptr, 0x0a)
                dst := add(dst, 0x01)
                mcopy(dst, add(len2, 0x20), mload(len2))
                dst := add(dst, mload(len2))
                mstore(dst, hex"080212") // TODO: remove padding
                switch contentLength
                case 0 { dst := add(dst, 0x02) }
                default {
                    dst := add(dst, 0x03)
                    mcopy(dst, add(len, 0x20), mload(len))
                    dst := add(dst, mload(len))
                    mcopy(dst, add(contentString, 0x20), contentLength)
                    dst := add(dst, contentLength)
                }
                mstore8(dst, 0x18)
                dst := add(dst, 0x01)
                mcopy(dst, add(len, 0x20), mload(len))
                dst := add(dst, mload(len))
                if or(xor(returndatasize(), 0x20), iszero(staticcall(gas(), 0x02, ptr, sub(dst, ptr), ptr, 0x20))) {
                    invalid()
                }
                r := mload(ptr)
            }
        }
    }

    /// @return r string.concat("ipfs://", Base58(bytes.concat(hex"1220", h)))
    /// @param h The SHA256 hash value to be encoded. Must be the output of `ipfsDagPbUnixFsHash`
    function CIDv0(bytes32 h) internal pure returns (string memory r) {
        assembly ("memory-safe") {
            // we're going to take total control of the first 4 words of
            // memory. we will restore the free memory pointer and the zero word
            // at the end
            r := mload(0x40)
            let ptr := add(r, 0x54)

            // store the base58 alphabet lookup table
            mstore(0x19, 0x31323334353637383941424344454647484a4b4c4d4e50515253)
            mstore(0x39, 0x5455565758595a6162636465666768696a6b6d6e6f707172737475767778797a)

            // the first 3 iterations are special because we're actually encoding 34 bytes
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 0x01)
            h := add(0x04, div(h, 0x3a)) // 0x04 is the residue of prepending `hex"1220"`
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 0x01)
            h := add(0x28, div(h, 0x3a)) // 0x28 is the residue of prepending `hex"1220"`
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 0x01)
            h := div(h, 0x3a)
            // this absurd constant prepends `hex"1220"` to `h`
            h := add(h, 0x616868b6a3c45673102217be3fec84b7db78d8bb82965f94d9f33718a8074e3)

            // the rest is "normal"
            for { let end := sub(ptr, 0x2b) } gt(ptr, end) { ptr := sub(ptr, 0x01) } {
                mstore8(ptr, mload(mod(h, 0x3a)))
                h := div(h, 0x3a)
            }

            mstore(r, 0x00)
            // length plus "ipfs://"
            mstore(add(r, 0x07), 0x35697066733a2f2f)
            mstore(0x40, add(r, 0x55))
            mstore(0x60, 0x00)
        }
    }

    function _protobufVarint(uint256 x) private pure returns (bytes memory r) {
        if (x >= 0x200000) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }
        assembly ("memory-safe") {
            r := mload(0x40)
            let length := 0x01
            mstore8(add(r, 0x20), or(0x80, and(0x7f, x)))
            x := shr(0x07, x)
            if x {
                mstore8(add(r, 0x21), or(0x80, and(0x7f, x)))
                x := shr(0x07, x)
                switch x
                case 0 { length := 0x02 }
                default {
                    mstore8(add(r, 0x22), and(0x7f, x))
                    length := 0x03
                }
            }

            mstore(r, length)
            let last := add(r, length)
            mstore(last, and(0xffffff7f, mload(last)))
            mstore(0x40, add(last, 0x20))
        }
    }
}

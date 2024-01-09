// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {UnsafeMath} from "../utils/UnsafeMath.sol";

library verifyIPFS {
    using UnsafeMath for uint256;

    function ipfsHash(string memory contentString) internal view returns (bytes32 r) {
        bytes memory len = protobufVarint(bytes(contentString).length);
        bytes memory len2 = protobufVarint(bytes(contentString).length + 4 + 2 * len.length);
        assembly ("memory-safe") {
            function _memcpy(_dst, _src, _len) {
                if or(xor(returndatasize(), _len), iszero(staticcall(gas(), 0x04, _src, _len, _dst, _len))) {
                    invalid()
                }
            }

            let ptr := mload(0x40)
            let dst := ptr
            mstore8(ptr, 0x0a)
            dst := add(dst, 0x01)
            mstore(add(dst, mload(len2)), hex"080212")
            _memcpy(dst, add(len2, 0x20), mload(len2))
            dst := add(dst, add(0x03, mload(len2)))
            _memcpy(dst, add(len, 0x20), mload(len))
            dst := add(dst, mload(len))
            _memcpy(dst, add(contentString, 0x20), mload(contentString))
            dst := add(dst, mload(contentString))
            mstore8(dst, 0x18)
            dst := add(dst, 0x01)
            _memcpy(dst, add(len, 0x20), mload(len))
            dst := add(dst, mload(len))
            if or(xor(returndatasize(), 0x20), iszero(staticcall(gas(), 0x02, ptr, sub(dst, ptr), ptr, 0x20))) {
                invalid()
            }
            r := mload(ptr)
        }
    }

    function base58sha256multihash(bytes32 h) internal pure returns (bytes memory r) {
        assembly ("memory-safe") {
            // we're going to take total control of the first 4 words of
            // memory. we will restore the free memory pointer and the zero word
            // at the end
            r := mload(0x40)
            let ptr := add(r, 0x4d)

            // store the base58 alphabet lookup table
            mstore(0x19, 0x31323334353637383941424344454647484a4b4c4d4e50515253)
            mstore(0x39, 0x5455565758595a6162636465666768696a6b6d6e6f707172737475767778797a)

            // the first 3 iterations are special because we're actually encoding 34 bytes
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := add(0x04, div(h, 0x3a)) // 0x04 is the residue of prepending `hex"1220"`
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := add(0x28, div(h, 0x3a)) // 0x28 is the residue of prepending `hex"1220"`
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            // this absurd constant prepends `hex"1220"` to `h`
            h := add(h, 0x616868b6a3c45673102217be3fec84b7db78d8bb82965f94d9f33718a8074e3)

            // the rest is "normal"
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            mstore8(ptr, mload(mod(h, 0x3a)))
            ptr := sub(ptr, 1)
            h := div(h, 0x3a)
            mstore8(ptr, mload(mod(h, 0x3a)))

            mstore(r, 0x2e)
            mstore(0x40, add(r, 0x4e))
            mstore(0x60, 0x00)
        }
    }

    function protobufVarint(uint256 x) internal pure returns (bytes memory r) {
        unchecked {
            // compute byte length
            uint256 length;
            if (x >> 14 >= 1) {
                length += 14;
            }
            if (x >> 7 >= 1 << length) {
                length += 7;
            }
            if (x >= 1 << length) {
                length += 7;
            }
            length = length.unsafeDiv(7);

            // format as bytes
            assembly ("memory-safe") {
                // TODO: golf this
                r := mload(0x40)
                mstore(r, length)
                mstore8(add(r, 0x20), or(0x80, and(0x7f, x)))
                x := shr(7, x)
                mstore8(add(r, 0x21), or(0x80, and(0x7f, x)))
                x := shr(7, x)
                mstore8(add(r, 0x22), or(0x80, and(0x7f, x)))
                x := shr(7, x)
                mstore8(add(r, 0x23), or(0x80, and(0x7f, x)))
                x := shr(7, x)

                let last := add(r, length)
                mstore(last, and(0xffffffff7f, mload(last)))

                mstore(0x40, add(last, 0x20))
            }
        }
    }
}

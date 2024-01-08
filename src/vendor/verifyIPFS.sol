pragma solidity ^0.8.0;

/// @title verifyIPFS
/// @author Martin Lundfall (martin.lundfall@gmail.com)
library verifyIPFS {
    function ipfsHash(string memory contentString) internal view returns (bytes32 r) {
        bytes memory len = lengthEncode(bytes(contentString).length);
        bytes memory len2 = lengthEncode(bytes(contentString).length + 6 * len.length);
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

    function lengthEncode(uint256 length) internal pure returns (bytes memory) {
        if (length < 128) {
            return to_binary(length);
        } else {
            return bytes.concat(to_binary(length % 128 + 128), to_binary(length / 128));
        }
    }

    function to_binary(uint256 x) internal pure returns (bytes memory r) {
        unchecked {
            // compute byte length
            uint256 length;
            if (x >> 16 >= 1 << length) {
                length += 16;
            }
            if (x >> 8 >= 1 << length) {
                length += 8;
            }
            if (x >= 1 << length) {
                length += 8;
            }
            length >>= 3;

            // swap endianness
            x = ((x & 0xFF00FF00) >> 8) | ((x & 0x00FF00FF) << 8);
            x = (x >> 16) | (x << 16);
            x <<= 224; // left align

            // format as bytes
            assembly ("memory-safe") {
                r := mload(0x40)
                mstore(r, length)
                mstore(add(r, 0x20), x)
                mstore(0x40, add(add(r, 0x20), length))
            }
        }
    }
}

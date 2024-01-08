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

    /// @dev Converts hex string to base 58
    function toBase58(bytes32 h) internal pure returns (bytes memory r) {
        assembly ("memory-safe") {
            r := mload(0x40)
            let ptr := add(r, 0x4d)

            // TODO: align so that we don't need padding
            mstore(0x1f, "123456789ABCDEFGHJKLMNPQRSTUVWXY")
            mstore(0x3f, "Zabcdefghijkmnopqrstuvwxyz")

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
            return concat(to_binary(length % 128 + 128), to_binary(length / 128));
        }
    }

    function concat(bytes memory byteArray, bytes memory byteArray2) internal pure returns (bytes memory) {
        bytes memory returnArray = new bytes(byteArray.length + byteArray2.length);
        uint256 i = 0;
        for (i; i < byteArray.length; i++) {
            returnArray[i] = byteArray[i];
        }
        for (i; i < (byteArray.length + byteArray2.length); i++) {
            returnArray[i] = byteArray2[i - byteArray.length];
        }
        return returnArray;
    }

    function to_binary(uint256 x) internal pure returns (bytes memory) {
        if (x == 0) {
            return new bytes(0);
        } else {
            bytes1 s = bytes1(uint8(x % 256));
            bytes memory r = new bytes(1);
            r[0] = s;
            return concat(to_binary(x / 256), r);
        }
    }
}

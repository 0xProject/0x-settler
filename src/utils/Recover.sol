// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

struct PackedSignature {
    bytes32 r;
    bytes32 vs;
}

library Recover {
    function recover(bytes32 signingHash, PackedSignature calldata sig) internal view returns (address recovered) {
        (bytes32 r, bytes32 vs) = (sig.r, sig.vs);

        assembly ("memory-safe") {
            let ptr := mload(0x40)

            mstore(0x00, signingHash)
            mstore(0x20, add(0x1b, shr(0xff, vs)))
            mstore(0x40, r)
            mstore(0x60, and(0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, vs))

            pop(staticcall(gas(), 0x01, 0x00, 0x80, 0x00, 0x20))
            recovered := mul(mload(0x00), eq(returndatasize(), 0x20))

            // restore cloberred memory
            mstore(0x40, ptr)
            mstore(0x60, 0x00)
        }
    }

    function recover(bytes memory payload, PackedSignature calldata sig) internal view returns (address) {
        return recover(keccak256(payload), sig);
    }

    function packSignature(uint8 v, bytes32 r, bytes32 s) internal pure returns (PackedSignature memory) {
        return PackedSignature({r: r, vs: bytes32(uint256(uint8(v) - 27) << 255 | uint256(s))});
    }
}

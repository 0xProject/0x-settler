// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {Panic} from "./Panic.sol";

library AddressDerivation {
    uint256 internal constant _SECP256K1_N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141;

    // keccak256(abi.encodePacked(ECMUL([x, y], k)))[12:]
    function deriveEOA(uint256 x, uint256 y, uint256 k) internal pure returns (address) {
        if (k == 0) {
            Panic.panic(Panic.DIVISION_BY_ZERO);
        }
        if (k >= _SECP256K1_N) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }

        unchecked {
            // https://ethresear.ch/t/you-can-kinda-abuse-ecrecover-to-do-ecmul-in-secp256k1-today/2384
            return ecrecover(bytes32(0), 27 + uint8(y & 1), bytes32(x), bytes32(mulmod(x, k, _SECP256K1_N)));
        }
    }

    // keccak256(RLP([deployer, nonce]))[12:]
    function deriveContract(address deployer, uint64 nonce) internal pure returns (address result) {
        if (nonce == type(uint64).max) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }
        if (nonce == 0) {
            assembly ("memory-safe") {
                mstore(0x14, and(0xffffffffffffffffffffffffffffffffffffffff, deployer))
                mstore(0x00, 0xd694)
                mstore8(0x34, 0x80)
                result := keccak256(0x1e, 0x17)
            }
        } else if (nonce < 0x80) {
            assembly ("memory-safe") {
                mstore(0x14, and(0xffffffffffffffffffffffffffffffffffffffff, deployer))
                mstore(0x00, 0xd694)
                mstore8(0x34, nonce)
                result := keccak256(0x1e, 0x17)
            }
        } else {
            uint256 nonceLength;
            unchecked {
                // compute ceil(log_256(nonce))
                if ((nonce >> 32) != 0) {
                    nonceLength = 4;
                }
                if ((nonce >> 16) >= (1 << (nonceLength << 3))) {
                    nonceLength += 2;
                }
                if ((nonce >> 8) >= (1 << (nonceLength << 3))) {
                    nonceLength += 1;
                }
                // ceil
                if (nonce >= (1 << (nonceLength << 3))) {
                    nonceLength += 1;
                }
            }
            assembly ("memory-safe") {
                mstore(add(0x01, nonceLength), nonce)
                mstore8(0x20, add(0x80, nonceLength))
                mstore(0x00, and(0xffffffffffffffffffffffffffffffffffffffff, deployer))
                mstore8(0x0a, add(0xd6, nonceLength))
                mstore8(0x0b, 0x94)
                result := keccak256(0x0a, add(0x17, nonceLength))
            }
        }
    }

    // keccak256(abi.encodePacked(bytes1(0xff), deployer, salt, initHash))[12:]
    function deriveDeterministicContract(address deployer, bytes32 salt, bytes32 initHash)
        internal
        pure
        returns (address result)
    {
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(ptr, and(0xffffffffffffffffffffffffffffffffffffffff, deployer))
            mstore8(add(ptr, 0x0b), 0xff)
            mstore(add(ptr, 0x20), salt)
            mstore(add(ptr, 0x40), initHash)
            result := keccak256(add(ptr, 0x0b), 0x55)
        }
    }
}

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Panic} from "./Panic.sol";
import {UnsafeMath} from "./UnsafeMath.sol";

library AddressDerivation {
    using UnsafeMath for uint256;

    uint256 internal constant _SECP256K1_P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F;
    uint256 internal constant _SECP256K1_N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141;
    uint256 internal constant SECP256K1_GX = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798;
    uint256 internal constant SECP256K1_GY = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8;

    error InvalidCurve(uint256 x, uint256 y);

    // keccak256(abi.encodePacked(ECMUL([x, y], k)))[12:]
    function deriveEOA(uint256 x, uint256 y, uint256 k) internal pure returns (address) {
        if (k == 0) {
            Panic.panic(Panic.DIVISION_BY_ZERO);
        }
        if (k >= _SECP256K1_N || x >= _SECP256K1_P || y >= _SECP256K1_P) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }

        // +/-7 are neither square nor cube mod p, so we only have to check one
        // coordinate against 0. if it is 0, then the other is too (the point at
        // infinity) or the point is invalid
        if (
            x == 0
                || y.unsafeMulMod(y, _SECP256K1_P)
                    != x.unsafeMulMod(x, _SECP256K1_P).unsafeMulMod(x, _SECP256K1_P).unsafeAddMod(7, _SECP256K1_P)
        ) {
            revert InvalidCurve(x, y);
        }

        unchecked {
            // https://ethresear.ch/t/you-can-kinda-abuse-ecrecover-to-do-ecmul-in-secp256k1-today/2384
            return ecrecover(
                bytes32(0), uint8(27 + (y & 1)), bytes32(x), bytes32(UnsafeMath.unsafeMulMod(x, k, _SECP256K1_N))
            );
        }
    }

    // keccak256(RLP([deployer, nonce]))[12:]
    function deriveContract(address deployer, uint64 nonce) internal pure returns (address result) {
        if (nonce == 0) {
            assembly ("memory-safe") {
                mstore(
                    0x00,
                    or(
                        0xd694000000000000000000000000000000000000000080,
                        shl(8, and(0xffffffffffffffffffffffffffffffffffffffff, deployer))
                    )
                )
                result := keccak256(0x09, 0x17)
            }
        } else if (nonce < 0x80) {
            assembly ("memory-safe") {
                // we don't care about dirty bits in `deployer`; they'll be overwritten later
                mstore(0x14, deployer)
                mstore(0x00, 0xd694)
                mstore8(0x34, nonce)
                result := keccak256(0x1e, 0x17)
            }
        } else {
            // compute ceil(log_256(nonce)) + 1
            uint256 nonceLength = 8;
            unchecked {
                if ((uint256(nonce) >> 32) != 0) {
                    nonceLength += 32;
                    if (nonce == type(uint64).max) {
                        Panic.panic(Panic.ARITHMETIC_OVERFLOW);
                    }
                }
                if ((uint256(nonce) >> 8) >= (1 << nonceLength)) {
                    nonceLength += 16;
                }
                if (uint256(nonce) >= (1 << nonceLength)) {
                    nonceLength += 8;
                }
                // ceil
                if ((uint256(nonce) << 8) >= (1 << nonceLength)) {
                    nonceLength += 8;
                }
                // bytes, not bits
                nonceLength >>= 3;
            }
            assembly ("memory-safe") {
                // we don't care about dirty bits in `deployer` or `nonce`. they'll be overwritten later
                mstore(nonceLength, nonce)
                mstore8(0x20, add(0x7f, nonceLength))
                mstore(0x00, deployer)
                mstore8(0x0a, add(0xd5, nonceLength))
                mstore8(0x0b, 0x94)
                result := keccak256(0x0a, add(0x16, nonceLength))
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

            // we don't care about dirty bits in `deployer`; they'll be overwritten later
            mstore(0x00, deployer)
            mstore(0x20, salt)
            mstore(0x40, initHash)
            mstore8(0x0b, 0xff)

            result := keccak256(0x0b, 0x55)

            mstore(0x40, ptr)
        }
    }

    function deriveContractEraVm(address deployer, uint64 nonce) internal pure returns (address result) {
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(ptr, 0x63bae3a9951d38e8a3fbb7b70909afc1200610fc5bc55ade242f815974674f23)
            mstore(add(0x20, ptr), and(0xffffffffffffffffffffffffffffffffffffffff, deployer))
            mstore(add(0x40, ptr), and(0xffffffffffffffff, nonce))
            result := keccak256(ptr, 0x60)
        }
    }

    function deriveDeterministicContractEraVm(
        address deployer,
        bytes32 salt,
        bytes32 initCodeWithoutArgsHash,
        bytes32 initArgsHash
    ) internal pure returns (address result) {
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(ptr, 0x2020dba91b30cc0006188af794c2fb30dd8520db7e2c088b7fc7c103c00ca494)
            mstore(add(0x20, ptr), and(0xffffffffffffffffffffffffffffffffffffffff, deployer))
            mstore(add(0x40, ptr), salt)
            mstore(add(0x60, ptr), initCodeWithoutArgsHash)
            mstore(add(0x80, ptr), initArgsHash)
            result := keccak256(ptr, 0xa0)
        }
    }
}

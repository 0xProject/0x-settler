// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import {LibRLP} from "@solady/utils/LibRLP.sol";

import {UnsafeMath} from "src/utils/UnsafeMath.sol";
import {FastLogic} from "src/utils/FastLogic.sol";

struct AccessListElem {
    address account;
    bytes32[] slots;
}

library LibAccessList {
    using LibRLP for LibRLP.List;
    using UnsafeMath for uint256;

    function encode(AccessListElem[] memory accessList) internal pure returns (LibRLP.List memory list) {
        uint256 accountsLength = accessList.length;
        for (uint256 i; i < accountsLength; i = i.unsafeInc()) {
            AccessListElem memory elem = accessList[i];
            LibRLP.List memory slots;
            uint256 slotsLength = elem.slots.length;
            for (uint256 j; j < slotsLength; j = j.unsafeInc()) {
                slots.p(bytes.concat(elem.slots[j]));
            }
            list.p(LibRLP.p().p(elem.account).p(slots));
        }
    }
}

using LibAccessList for AccessListElem[];

struct PackedSignature {
    bytes32 r;
    bytes32 vs;
}

library TransactionEncoder {
    using LibRLP for LibRLP.List;
    using UnsafeMath for uint256;
    using FastLogic for bool;

    error InvalidTransaction();

    uint256 internal constant _SECP256K1_N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141;

    function _recover(bytes memory payload, uint8 v, bytes32 r, bytes32 s) private view returns (address) {
        bytes32 signingHash = keccak256(payload);
        address recovered = ecrecover(signingHash, v, r, s);
        if (recovered == address(0)) {
            revert InvalidTransaction();
        }
        return recovered;
    }

    function _check(uint256 nonce, uint256 gasLimit, PackedSignature calldata sig)
        private
        pure
        returns (uint8 v, bytes32 r, bytes32 s)
    {
        bytes32 vs;
        (r, vs) = (sig.r, sig.vs);
        unchecked {
            v = uint8(uint256(vs) >> 255) + 27;
        }
        s = vs & 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff;
        if (
            (nonce >= type(uint64).max).or(gasLimit > 30_000_000).or(r == bytes32(0)).or(uint256(r) >= _SECP256K1_N).or(
                s == bytes32(0)
            ).or(uint256(s) > _SECP256K1_N / 2)
        ) {
            revert InvalidTransaction();
        }
    }

    // EIP-155
    function recoverSigner(
        uint256 nonce,
        uint256 gasPrice,
        uint256 gasLimit,
        address payable to,
        uint256 value,
        bytes memory data,
        PackedSignature calldata sig
    ) internal view returns (address) {
        (uint8 v, bytes32 r, bytes32 s) = _check(nonce, gasLimit, sig);
        bytes memory encoded = LibRLP.p(nonce).p(gasPrice).p(gasLimit).p(to).p(value).p(data).p(block.chainid).p(
            uint256(0)
        ).p(uint256(0)).encode();
        return _recover(encoded, v, r, s);
    }

    // EIP-2930
    function recoverSigner(
        uint256 nonce,
        uint256 gasPrice,
        uint256 gasLimit,
        address payable to,
        uint256 value,
        bytes memory data,
        AccessListElem[] memory accessList,
        PackedSignature calldata sig
    ) internal view returns (address) {
        (uint8 v, bytes32 r, bytes32 s) = _check(nonce, gasLimit, sig);
        bytes memory encoded = bytes.concat(
            bytes1(0x01),
            LibRLP.p(block.chainid).p(nonce).p(gasPrice).p(gasLimit).p(to).p(value).p(data).p(accessList.encode())
                .encode()
        );
        return _recover(encoded, v, r, s);
    }

    // EIP-1559
    function recoverSigner(
        uint256 nonce,
        uint256 gasPriorityPrice,
        uint256 gasPrice,
        uint256 gasLimit,
        address payable to,
        uint256 value,
        bytes memory data,
        AccessListElem[] memory accessList,
        PackedSignature calldata sig
    ) internal view returns (address) {
        (uint8 v, bytes32 r, bytes32 s) = _check(nonce, gasLimit, sig);
        bytes memory encoded = bytes.concat(
            bytes1(0x02),
            LibRLP.p(block.chainid).p(nonce).p(gasPriorityPrice).p(gasPrice).p(gasLimit).p(to).p(value).p(data).p(
                accessList.encode()
            ).encode()
        );
        return _recover(encoded, v, r, s);
    }
}

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import {LibRLP} from "@solady/utils/LibRLP.sol";
import {LibBit} from "@solady/utils/LibBit.sol";

import {UnsafeMath} from "./UnsafeMath.sol";
import {FastLogic} from "./FastLogic.sol";

struct AccessListElem {
    address account;
    bytes32[] slots;
}

type AccessListIterator is uint256;
type SlotListIterator is uint256;

library LibAccessList {
    using LibRLP for LibRLP.List;

    function iter(AccessListElem[] calldata a) internal pure returns (AccessListIterator r) {
        assembly ("memory-safe") {
            r := a.offset
        }
    }

    function iter(bytes32[] calldata a) internal pure returns (SlotListIterator r) {
        assembly ("memory-safe") {
            r := a.offset
        }
    }

    function next(AccessListIterator i) internal pure returns (AccessListIterator) {
        unchecked {
            return AccessListIterator.wrap(AccessListIterator.unwrap(i) + 32);
        }
    }

    function next(SlotListIterator i) internal pure returns (SlotListIterator) {
        unchecked {
            return SlotListIterator.wrap(SlotListIterator.unwrap(i) + 32);
        }
    }

    function end(AccessListElem[] calldata a) internal pure returns (AccessListIterator r) {
        unchecked {
            return AccessListIterator.wrap((a.length << 5) + AccessListIterator.unwrap(iter(a)));
        }
    }

    function end(bytes32[] calldata a) internal pure returns (SlotListIterator r) {
        unchecked {
            return SlotListIterator.wrap((a.length << 5) + SlotListIterator.unwrap(iter(a)));
        }
    }

    function get(AccessListElem[] calldata a, AccessListIterator i) internal pure returns (address account, bytes32[] calldata slots) {
        assembly ("memory-safe") {
            let r := add(a.offset, calldataload(i))
            account := calldataload(r)
            if shr(0xa0, account) { revert(0x00, 0x00) }
            slots.offset := add(r, calldataload(add(0x20, r)))
            slots.length := calldataload(slots.offset)
            slots.offset := add(0x20, slots.offset)
        }
    }

    function get(bytes32[] calldata, SlotListIterator i) internal pure returns (bytes32 slot) {
        assembly ("memory-safe") {
            slot := calldataload(i)
        }
    }

    function encode(AccessListElem[] calldata accessList) internal pure returns (LibRLP.List memory list) {
        for ((AccessListIterator i, AccessListIterator i_end) = (accessList.iter(), accessList.end()); i != i_end; i = i.next()) {
            (address account, bytes32[] calldata slots_src) = accessList.get(i);
            LibRLP.List memory slots_dst;
            for ((SlotListIterator j, SlotListIterator j_end) = (slots_src.iter(), slots_src.end()); j != j_end; j = j.next()) {
                slots_dst.p(abi.encode(slots_src.get(j)));
            }
            list.p(LibRLP.p(account).p(slots_dst));
        }
    }
}

function __AccessListIterator_eq(AccessListIterator a, AccessListIterator b) pure returns (bool) {
    return AccessListIterator.unwrap(a) == AccessListIterator.unwrap(b);
}

function __AccessListIterator_ne(AccessListIterator a, AccessListIterator b) pure returns (bool) {
    return AccessListIterator.unwrap(a) != AccessListIterator.unwrap(b);
}

using {__AccessListIterator_eq as ==, __AccessListIterator_ne as !=} for AccessListIterator global;


function __SlotListIterator_eq(SlotListIterator a, SlotListIterator b) pure returns (bool) {
    return SlotListIterator.unwrap(a) == SlotListIterator.unwrap(b);
}

function __SlotListIterator_ne(SlotListIterator a, SlotListIterator b) pure returns (bool) {
    return SlotListIterator.unwrap(a) != SlotListIterator.unwrap(b);
}

using {__SlotListIterator_eq as ==, __SlotListIterator_ne as !=} for SlotListIterator global;

using LibAccessList for AccessListElem[];
using LibAccessList for bytes32[];
using LibAccessList for AccessListIterator;
using LibAccessList for SlotListIterator;

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

    function _recover(bytes memory payload, uint8 v, bytes32 r, bytes32 s) private pure returns (address) {
        bytes32 signingHash = keccak256(payload);
        address recovered = ecrecover(signingHash, v, r, s);
        if (recovered == address(0)) {
            revert InvalidTransaction();
        }
        return recovered;
    }

    function _check(uint256 nonce, uint256 gasLimit, uint256 calldataGas, uint256 extraGas, PackedSignature calldata sig)
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
            (nonce >= type(uint64).max).or(gasLimit < calldataGas.unsafeAdd(21_000) + extraGas).or(gasLimit > 30_000_000).or(r == bytes32(0)).or(uint256(r) >= _SECP256K1_N).or(
                s == bytes32(0)
            ).or(uint256(s) > _SECP256K1_N / 2)
        ) {
            revert InvalidTransaction();
        }
    }

    function _slice(bytes memory data, uint256 i) internal pure returns (bytes32 r) {
        assembly ("memory-safe") {
            r := mload(add(add(0x20, data), i))
        }
    }

    function _calldataGas(bytes memory data) private pure returns (uint256) {
        unchecked {
            uint256 zeroBytes;
            uint256 length = data.length - 32;
            uint256 i;
            for (; i < length; i += 32) {
                zeroBytes += LibBit.countZeroBytes(uint256(_slice(data, i)));
            }
            uint256 padding = i - length;
            zeroBytes += LibBit.countZeroBytes(uint256(_slice(data, i)) >> (padding << 3)) - padding;
            return (data.length << 4) - zeroBytes * 12;
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
        PackedSignature calldata sig,
        uint256 extraGas
    ) internal view returns (address) {
        (uint8 v, bytes32 r, bytes32 s) = _check(nonce, gasLimit, _calldataGas(data), extraGas, sig);
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
        AccessListElem[] calldata accessList,
        PackedSignature calldata sig,
        uint256 extraGas
    ) internal view returns (address) {
        (uint8 v, bytes32 r, bytes32 s) = _check(nonce, gasLimit, _calldataGas(data), extraGas, sig);
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
        AccessListElem[] calldata accessList,
        PackedSignature calldata sig,
        uint256 extraGas
    ) internal view returns (address) {
        (uint8 v, bytes32 r, bytes32 s) = _check(nonce, gasLimit, _calldataGas(data), extraGas, sig);
        bytes memory encoded = bytes.concat(
            bytes1(0x02),
            LibRLP.p(block.chainid).p(nonce).p(gasPriorityPrice).p(gasPrice).p(gasLimit).p(to).p(value).p(data).p(
                accessList.encode()
            ).encode()
        );
        return _recover(encoded, v, r, s);
    }
}

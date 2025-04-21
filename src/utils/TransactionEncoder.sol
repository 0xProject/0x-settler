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

library TransactionEncoder {
    using LibRLP for LibRLP.List;
    using UnsafeMath for uint256;
    using FastLogic for bool;

    error InvalidTransaction();

    uint256 internal constant _SECP256K1_N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141;

    function recoverSigner155(
        uint256 nonce, // TODO: up to 2 ** 64 - 2
        uint256 gasPrice,
        uint256 gasLimit, // TODO: up to 30M; check against intrinsic gas
        address payable to,
        uint256 value,
        bytes memory data,
        uint256 v,
        bytes32 r,
        bytes32 s
    ) internal view returns (address) {
        uint256 eip155ChainId;
        unchecked {
            eip155ChainId = block.chainid * 2 + 35;
        }
        if ((v != eip155ChainId).and(v != eip155ChainId.unsafeInc()).or(r == bytes32(0)).or(uint256(r) >= _SECP256K1_N).or(s == bytes32(0)).or(uint256(s) > _SECP256K1_N / 2)) {
            revert InvalidTransaction();
        }
        unchecked {
            v -= 8 + block.chainid * 2;
        }
        bytes memory encoded = LibRLP.p().p(nonce).p(gasPrice).p(gasLimit).p(to).p(value).p(data).p(block.chainid).p(uint256(0)).p(uint256(0)).encode();
        bytes32 signingHash = keccak256(encoded);
        address recovered = ecrecover(signingHash, uint8(v), bytes32(r), bytes32(s));
        if (recovered == address(0)) {
            revert InvalidTransaction();
        }
        return recovered;
    }

    function recoverSigner1559(
        uint256 nonce,
        uint256 gasPriorityPrice,
        uint256 gasPrice,
        uint256 gasLimit,
        address payable to,
        uint256 value,
        bytes memory data,
        AccessListElem[] memory accessList,
        uint256 v,
        bytes32 r,
        bytes32 s
    ) internal view returns (address) {
        if ((v >> 1 != 0).or(r == bytes32(0)).or(uint256(r) >= _SECP256K1_N).or(s == bytes32(0)).or(uint256(s) > _SECP256K1_N / 2)) {
            revert InvalidTransaction();
        }
        unchecked {
            v += 27;
        }
        bytes memory encoded = bytes.concat(bytes1(0x02), LibRLP.p().p(block.chainid).p(nonce).p(gasPriorityPrice).p(gasPrice).p(gasLimit).p(to).p(value).p(data).p(accessList.encode()).encode());
        bytes32 signingHash = keccak256(encoded);
        address recovered = ecrecover(signingHash, uint8(v), bytes32(r), bytes32(s));
        if (recovered == address(0)) {
            revert InvalidTransaction();
        }
        return recovered;
    }
}

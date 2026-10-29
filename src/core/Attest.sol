// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Select} from "./Select.sol";
import {ISettlerActions} from "../ISettlerActions.sol";
import {IAttestation} from "../interfaces/IAttestation.sol";
import {TransientStorage} from "./Permit2Payment.sol";
import {Cuid} from "../utils/Cuid.sol";
import {FastLogic} from "../utils/FastLogic.sol";

abstract contract Attest is Select {
    using FastLogic for bool;

    bytes32 private constant _AUTHORITY_SLOT =
        bytes32(uint256(uint96(uint256(keccak256("attestation authority slot")) - 1)));
    bytes32 private constant _ATTESTATION_SLOT =
        bytes32(uint256(uint96(uint256(keccak256("attestation metadata slot")) - 1)));
    bytes32 private constant _TYPEHASH =
        keccak256("Attestation(address taker,uint256 deadline,bytes12 zid,string appid)");
    bytes32 private constant _DOMAIN_TYPEHASH =
        keccak256("EIP712Domain(string name,uint256 chainId,address verifyingContract)");
    bytes32 private constant _NAME_HASH = keccak256("0xSettler");
    bytes32 private immutable _DOMAIN_SEPARATOR;

    constructor() {
        _DOMAIN_SEPARATOR = _domainSeparator(_chainId());
    }

    function _domainSeparator(uint256 chainId) private view returns (bytes32 domain) {
        bytes32 domainTypeHash = _DOMAIN_TYPEHASH;
        bytes32 nameHash = _NAME_HASH;
        // domain = keccak256(abi.encode(domainTypeHash, nameHash, chainId, address(this))).
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(0x00, domainTypeHash)
            mstore(0x20, nameHash)
            mstore(0x40, chainId)
            mstore(0x60, address())
            domain := keccak256(0x00, 0x80)
            mstore(0x40, ptr)
            mstore(0x60, 0x00)
        }
    }

    function _dispatch(uint256 i, uint256 action, bytes calldata data, AllowedSlippage memory slippage)
        internal
        virtual
        override
        returns (bool)
    {
        if (action == uint32(ISettlerActions.ATTEST.selector)) {
            (uint256 deadline, bytes32 r, bytes32 vs) = abi.decode(data, (uint256, bytes32, bytes32));
            _attest(deadline, r, vs);
            return true;
        }
        return super._dispatch(i, action, data, slippage);
    }

    function _fallback(bytes calldata data) internal virtual override returns (bool success, bytes memory returndata) {
        if (bytes4(data) == IAttestation.attestation.selector) {
            return (true, attestation());
        }
        return super._fallback(data);
    }

    function _attest(uint256 deadline, bytes32 r, bytes32 vs) private {
        // The free memory pointer is restored by hand because `FreeMemory` cannot be a base of this
        // contract: chain mixins linearize it between `SettlerBase` and `SettlerBase`'s parents.
        uint256 freeMemPtr;
        assembly ("memory-safe") {
            freeMemPtr := mload(0x40)
        }
        if ((block.timestamp > deadline).or(deadline >> 40 != 0)) {
            assembly ("memory-safe") {
                mstore(0x00, 0xcd21db4f) // selector for `SignatureExpired(uint256)`
                mstore(0x20, deadline)
                revert(0x1c, 0x24)
            }
        }
        bytes32 metadata;
        // Every swap entrypoint has this argument at the same offset:
        // metadata = abi.decode(msg.data[132:164], (bytes32)).
        assembly ("memory-safe") {
            metadata := calldataload(0x84)
        }
        address taker = _msgSender();
        string memory appid = Cuid.decode(uint128(uint256(metadata)));
        bytes32 typeHash = _TYPEHASH;
        bytes32 domain = block.chainid == _chainId() ? _DOMAIN_SEPARATOR : _domainSeparator(block.chainid);
        address authority;
        // structHash = keccak256(abi.encode(typeHash, taker, deadline, bytes12(metadata), keccak256(bytes(appid))));
        // digest = keccak256(abi.encodePacked(hex"1901", domain, structHash));
        // authority = ecrecover(digest, 27 + uint8(uint256(vs) >> 255), r, bytes32(uint256(vs) & (2**255 - 1)));
        // if (authority == address(0)) revert InvalidSignature();
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(ptr, typeHash)
            mstore(add(0x20, ptr), taker)
            mstore(add(0x0c, ptr), shl(0x60, typeHash)) // Clears `taker`'s padding.
            mstore(add(0x40, ptr), deadline)
            mstore(add(0x60, ptr), shl(0xa0, shr(0xa0, metadata)))
            mstore(add(0x80, ptr), keccak256(add(0x20, appid), mload(appid)))
            mstore(0x00, 0x1901)
            mstore(0x20, domain)
            mstore(0x40, keccak256(ptr, 0xa0))
            mstore(0x00, keccak256(0x1e, 0x42))
            mstore(0x20, add(0x1b, shr(0xff, vs)))
            mstore(0x40, r)
            mstore(0x60, and(0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, vs))
            authority := mload(staticcall(gas(), 0x01, 0x00, 0x80, 0x01, 0x20))
            // Successful recovery returns a 160-bit address in 32 bytes, so the product cannot overflow.
            if iszero(mul(returndatasize(), authority)) {
                mstore(0x00, 0x8baa579f) // selector for `InvalidSignature()`
                revert(0x1c, 0x04)
            }
            mstore(0x40, ptr)
            mstore(0x60, 0x00)
        }
        bytes32 authoritySlot = _AUTHORITY_SLOT;
        bytes32 attestationSlot = _ATTESTATION_SLOT;
        // transient[authoritySlot] = uint160(authority) | (deadline << 160); transient[attestationSlot] = metadata
        assembly ("memory-safe") {
            tstore(authoritySlot, or(shl(0xa0, deadline), authority))
            tstore(attestationSlot, metadata)
        }
        TransientStorage.setAttested();
        assembly ("memory-safe") {
            mstore(0x40, freeMemPtr)
        }
    }

    function attestation() internal view returns (bytes memory result) {
        address taker = TransientStorage.getAttestedPayer();
        bytes32 metadata;
        address authority;
        uint40 deadline;
        bytes32 authoritySlot = _AUTHORITY_SLOT;
        bytes32 attestationSlot = _ATTESTATION_SLOT;
        // (authority, deadline) = unpack(transient[authoritySlot]); metadata = transient[attestationSlot]
        assembly ("memory-safe") {
            authority := tload(authoritySlot)
            deadline := shr(0xa0, authority)
            metadata := tload(attestationSlot)
        }
        // The head is reserved first so that `Cuid.decode`, which allocates at the free memory
        // pointer, writes the length word and single data word of `appid` (at most 26 bytes)
        // directly into the tail
        // result = abi.encode(taker, bytes12(metadata), appid, authority, deadline).
        assembly ("memory-safe") {
            result := mload(0x40)
            mstore(0x40, add(0xc0, result))
        }
        Cuid.decode(uint128(uint256(metadata)));
        assembly ("memory-safe") {
            mstore(result, 0xe0)
            mstore(add(0x20, result), taker)
            mstore(add(0x0c, result), shl(0x60, 0xe0)) // Clears `taker`'s padding.
            mstore(add(0xa0, result), and(0xffffffffff, deadline))
            mstore(add(0x80, result), authority)
            mstore(add(0x6c, result), shl(0x60, 0xa0)) // Offset to `appid`; clears `authority`'s padding.
            mstore(add(0x40, result), metadata)
            mstore(add(0x4c, result), 0x00) // Clears `zid`'s padding and the offset's high bytes.
        }
    }
}

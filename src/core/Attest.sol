// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Select} from "./Select.sol";
import {ISettlerActions} from "../ISettlerActions.sol";
import {IAttestation} from "../interfaces/IAttestation.sol";
import {TransientStorage} from "./Permit2Payment.sol";
import {SignatureExpired, InvalidSignature} from "./SettlerErrors.sol";
import {Cuid} from "../utils/Cuid.sol";

abstract contract Attest is Select {
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

    function _domainSeparator(uint256 chainId) private view returns (bytes32) {
        return keccak256(abi.encode(_DOMAIN_TYPEHASH, _NAME_HASH, chainId, address(this)));
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
        if (block.timestamp > deadline) revert SignatureExpired(deadline);
        bytes32 metadata;
        // Every swap entrypoint has this argument at the same offset:
        // metadata = abi.decode(msg.data[132:164], (bytes32)).
        assembly ("memory-safe") {
            metadata := calldataload(0x84)
        }
        bytes32 structHash = keccak256(
            abi.encode(
                _TYPEHASH,
                _msgSender(),
                deadline,
                bytes12(metadata),
                keccak256(bytes(Cuid.decode(uint128(uint256(metadata)))))
            )
        );
        bytes32 domain = block.chainid == _chainId() ? _DOMAIN_SEPARATOR : _domainSeparator(block.chainid);
        bytes32 digest = keccak256(abi.encodePacked(hex"1901", domain, structHash));
        address authority;
        bool invalidSignature;
        // Invalid signatures can return no bytes, leaving the scratch data intact; require nonempty output:
        // authority = ecrecover(digest, 27 + uint8(uint256(vs) >> 255), r, bytes32(uint256(vs) & (2**255 - 1))).
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(0x00, digest)
            mstore(0x20, add(0x1b, shr(0xff, vs)))
            mstore(0x40, r)
            mstore(0x60, and(0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, vs))
            authority := mload(staticcall(gas(), 0x01, 0x00, 0x80, 0x01, 0x20))
            invalidSignature := or(iszero(returndatasize()), iszero(authority))
            mstore(0x40, ptr)
            mstore(0x60, 0x00)
        }
        if (invalidSignature) revert InvalidSignature();
        bytes32 authoritySlot = _AUTHORITY_SLOT;
        bytes32 attestationSlot = _ATTESTATION_SLOT;
        // These values are readable only while the payer's attestation bit is set:
        // transient[authoritySlot] = authority; transient[attestationSlot] = metadata.
        assembly ("memory-safe") {
            tstore(authoritySlot, authority)
            tstore(attestationSlot, metadata)
        }
        TransientStorage.setAttested();
    }

    function attestation() internal view returns (bytes memory) {
        address taker = TransientStorage.getAttestedPayer();
        bytes32 metadata;
        address authority;
        bytes32 authoritySlot = _AUTHORITY_SLOT;
        bytes32 attestationSlot = _ATTESTATION_SLOT;
        // Explicit slots match the attestation writes: authority = transient[authoritySlot]; metadata = transient[attestationSlot].
        assembly ("memory-safe") {
            authority := tload(authoritySlot)
            metadata := tload(attestationSlot)
        }
        return abi.encode(taker, bytes12(metadata), Cuid.decode(uint128(uint256(metadata))), authority);
    }
}

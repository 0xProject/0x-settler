// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.19;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {IERC20PermitCommon, IERC2612, IERC20PermitAllowed} from "../interfaces/IERC2612.sol";
import {IERC20MetaTransaction} from "../interfaces/INativeMetaTransaction.sol";
import {Revert} from "./Revert.sol";

library FastPermit {
    function fastPermit(
        IERC2612 token,
        address owner,
        address spender,
        uint256 amount,
        uint256 deadline,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) internal returns (bool success) {
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(ptr, 0xd505accf) // selector for `permit(address,address,uint256,uint256,uint8,bytes32,bytes32)`
            mstore(add(0x20, ptr), and(0xffffffffffffffffffffffffffffffffffffffff, owner))
            mstore(add(0x40, ptr), and(0xffffffffffffffffffffffffffffffffffffffff, spender))
            mstore(add(0x60, ptr), amount)
            mstore(add(0x80, ptr), deadline)
            mstore(add(0xa0, ptr), and(0xff, v))
            mstore(add(0xc0, ptr), r)
            mstore(add(0xe0, ptr), s)

            success := call(gas(), token, 0x00, add(0x1c, ptr), 0xe4, 0x00, 0x20)
            success := and(success, and(iszero(xor(mload(0x00), 0x01)), gt(returndatasize(), 0x1f)))
        }
    }

    function fastPermitAllowed(
        IERC20PermitAllowed token,
        address owner,
        address spender,
        uint256 nonce,
        uint256 expiry,
        bool allowed,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) internal returns (bool success) {
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(ptr, 0x8fcbaf0c) // selector for `permit(address,address,uint256,uint256,bool,uint8,bytes32,bytes32)`
            mstore(add(0x20, ptr), and(0xffffffffffffffffffffffffffffffffffffffff, owner))
            mstore(add(0x40, ptr), and(0xffffffffffffffffffffffffffffffffffffffff, spender))
            mstore(add(0x60, ptr), nonce)
            mstore(add(0x80, ptr), expiry)
            mstore(add(0xa0, ptr), allowed)
            mstore(add(0xc0, ptr), and(0xff, v))
            mstore(add(0xe0, ptr), r)
            mstore(add(0x100, ptr), s)

            success := call(gas(), token, 0x00, add(0x1c, ptr), 0x104, 0x00, 0x20)
            success := and(success, and(iszero(xor(mload(0x00), 0x01)), gt(returndatasize(), 0x1f)))
        }
    }

    function fastApproveMetaTransaction(
        IERC20MetaTransaction token,
        address owner,
        address spender,
        uint256 amount,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) internal returns (bool success, bytes32 functionSignatureHash) {
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(add(0xf8, ptr), amount)
            mstore(add(0xd8, ptr), spender)
            mstore(add(0xc4, ptr), 0x095ea7b3000000000000000000000000) // selector for `approve(address,uint256)` with `spender` padding
            mstore(add(0xb4, ptr), 0x44) // length of approve call
            mstore(add(0x94, ptr), and(0xff, v))
            mstore(add(0x74, ptr), s)
            mstore(add(0x54, ptr), r)
            mstore(add(0x34, ptr), 0xa0) // offset to function signature
            mstore(add(0x14, ptr), owner)
            mstore(ptr, 0x0c53c51c000000000000000000000000) // selector for `executeMetaTransaction(address,bytes,bytes32,bytes32,uint8)` with `owner` padding

            functionSignatureHash := keccak256(add(0xd4, ptr), 0x44)

            success := call(gas(), token, 0x00, add(0x10, ptr), 0x108, 0x00, 0x60)
            success := and(success, and(iszero(xor(mload(0x40), 0x01)), gt(returndatasize(), 0x5f)))

            mstore(0x40, ptr)
        }
    }

    function fastDomainSeparator(IERC20 token, bytes4 domainSeparatorSelector)
        internal
        view
        returns (bytes32 domainSeparator)
    {
        assembly ("memory-safe") {
            mstore(0x00, domainSeparatorSelector)
            if iszero(staticcall(gas(), token, 0x00, 0x04, 0x00, 0x20)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            if gt(0x20, returndatasize()) {
                revert(0x00, 0x00)
            }
            domainSeparator := mload(0x00)
        }
    }

    function fastNonce(IERC20 token, address owner, bytes4 nonceSelector) internal view returns (uint256 nonce) {
        assembly ("memory-safe") {
            mstore(0x00, nonceSelector)
            mstore(0x04, and(0xffffffffffffffffffffffffffffffffffffffff, owner))
            if iszero(staticcall(gas(), token, 0x00, 0x24, 0x00, 0x20)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            if gt(0x20, returndatasize()) {
                revert(0x00, 0x00)
            }
            nonce := mload(0x00)
        }
    }

    function fastAllowance(IERC20 token, address owner, address spender) internal view returns (uint256 allowance) {
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(0x00, 0xdd62ed3e) // selector for `allowance(address,address)`
            mstore(0x20, and(0xffffffffffffffffffffffffffffffffffffffff, owner))
            mstore(0x40, and(0xffffffffffffffffffffffffffffffffffffffff, spender))
            if iszero(staticcall(gas(), token, 0x1c, 0x44, 0x00, 0x20)) {
                let ptr_ := mload(0x40)
                returndatacopy(ptr_, 0x00, returndatasize())
                revert(ptr_, returndatasize())
            }
            if gt(0x20, returndatasize()) {
                revert(0x00, 0x00)
            }
            allowance := mload(0x00)
            mstore(0x40, ptr)
        }
    }
}

library SafePermit {
    using FastPermit for IERC2612;
    using FastPermit for IERC20PermitAllowed;
    using FastPermit for IERC20MetaTransaction;
    using FastPermit for IERC20;

    bytes32 private constant _PERMIT_TYPEHASH =
        keccak256("Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)");

    bytes32 private constant _PERMIT_ALLOWED_TYPEHASH =
        keccak256("Permit(address holder,address spender,uint256 nonce,uint256 expiry,bool allowed)");

    bytes32 private constant _META_TRANSACTION_TYPEHASH =
        keccak256("MetaTransaction(uint256 nonce,address from,bytes functionSignature)");

    function _revert(uint32 err) internal pure {
        assembly ("memory-safe") {
            mstore(0x00, err)
            revert(0x1c, 0x04)
        }
    }

    function _checkEffects(IERC20 token, address owner, address spender, uint256 amount, uint256 nonce) internal view {
        if (nonce == 0 || token.fastAllowance(owner, spender) != amount) {
            _revert(0xb78cb0dd); // selector for `PermitFailed()`
        }
    }

    function _checkSignature(bytes32 domainSeparator, address owner, bytes32 structHash, uint8 v, bytes32 r, bytes32 s)
        internal
        pure
    {
        bytes32 signingHash = keccak256(bytes.concat(bytes2("\x19\x01"), domainSeparator, structHash));
        address recovered = ecrecover(signingHash, v, r, s);
        if (recovered == address(0)) {
            _revert(0x8baa579f); // selector for `InvalidSignature()`
        }
        if (recovered != owner) {
            _revert(0x815e1d64); // selector for `InvalidSigner()`
        }
    }

    function safePermit(
        IERC2612 token,
        address owner,
        address spender,
        uint256 amount,
        uint256 deadline,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) internal {
        // `permit` could succeed vacuously with no returndata if there's a fallback
        // function (e.g. WETH). `permit` could fail spuriously if it was
        // replayed/frontrun. Avoid these by manually verifying the effects and
        // signature. Insufficient gas griefing is defused by checking the effects.
        if (!token.fastPermit(owner, spender, amount, deadline, v, r, s)) {
            // Check effects and signature
            if (block.timestamp > deadline) {
                _revert(0x1a15a3cc); // selector for `PermitExpired()`
            }
            uint256 nonce = token.fastNonce(owner, token.nonces.selector);
            _checkEffects(token, owner, spender, amount, nonce);
            unchecked {
                nonce--;
            }
            bytes32 structHash = keccak256(abi.encode(_PERMIT_TYPEHASH, owner, spender, amount, nonce, deadline));
            _checkSignature(token.fastDomainSeparator(token.DOMAIN_SEPARATOR.selector), owner, structHash, v, r, s);
        }
    }

    function safePermit(
        IERC20PermitAllowed token,
        address owner,
        address spender,
        uint256 nonce,
        uint256 deadline,
        bool allowed,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) internal {
        // See comments above
        if (!token.fastPermitAllowed(owner, spender, nonce, deadline, allowed, v, r, s)) {
            // Check effects and signature
            if (block.timestamp > deadline && deadline > 0) {
                _revert(0x1a15a3cc);
            }
            nonce = token.fastNonce(owner, token.nonces.selector);
            _checkEffects(token, owner, spender, allowed ? type(uint256).max : 0, nonce);
            unchecked {
                nonce--;
            }
            bytes32 structHash =
                keccak256(abi.encode(_PERMIT_ALLOWED_TYPEHASH, owner, spender, nonce, deadline, allowed));
            _checkSignature(token.fastDomainSeparator(token.DOMAIN_SEPARATOR.selector), owner, structHash, v, r, s);
        }
    }

    function safePermit(
        IERC20MetaTransaction token,
        address owner,
        address spender,
        uint256 amount,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) internal {
        // See comments above
        (bool success, bytes32 functionSignatureHash) =
            token.fastApproveMetaTransaction(owner, spender, amount, v, r, s);
        if (!success) {
            // Check effects and signature
            uint256 nonce = token.fastNonce(owner, token.getNonce.selector);
            _checkEffects(token, owner, spender, amount, nonce);
            unchecked {
                nonce--;
            }
            bytes32 structHash = keccak256(abi.encode(_META_TRANSACTION_TYPEHASH, nonce, owner, functionSignatureHash));
            _checkSignature(token.fastDomainSeparator(token.getDomainSeparator.selector), owner, structHash, v, r, s);
        }
    }
}

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {IERC20PermitCommon, IERC2612, IDAIStylePermit} from "../interfaces/IERC2612.sol";
import {IERC20MetaTransaction} from "../interfaces/INativeMetaTransaction.sol";
import {Revert} from "./Revert.sol";
import {FastLogic} from "./FastLogic.sol";

library FastPermit {
    function fastPermit(
        IERC2612 token,
        address owner,
        address spender,
        uint256 amount,
        uint256 deadline,
        bytes32 vs,
        bytes32 r
    ) internal returns (bool success) {
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(add(0xd4, ptr), and(0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, vs)) // `s`.
            mstore(add(0xb4, ptr), r) // `r`.
            mstore(add(0x94, ptr), add(0x1b, shr(0xff, vs))) // `v`.
            mstore(add(0x74, ptr), deadline)
            mstore(add(0x54, ptr), amount)
            mstore(add(0x34, ptr), spender)
            mstore(add(0x20, ptr), shl(0x60, owner)) // with `spender`'s padding
            mstore(ptr, 0xd505accf000000000000000000000000) // selector for `permit(address,address,uint256,uint256,uint8,bytes32,bytes32)` with `owner`'s padding

            success := call(gas(), token, 0x00, add(0x10, ptr), 0xe4, 0x00, 0x20)
            success := and(success, and(iszero(xor(mload(0x00), 0x01)), gt(returndatasize(), 0x1f)))
        }
    }

    function fastDAIPermit(
        IDAIStylePermit token,
        address owner,
        address spender,
        uint256 nonce,
        uint256 expiry,
        bool allowed,
        bytes32 vs,
        bytes32 r
    ) internal returns (bool success) {
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(add(0xf4, ptr), and(0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, vs)) // `s`.
            mstore(add(0xd4, ptr), r) // `r`.
            mstore(add(0xb4, ptr), add(0x1b, shr(0xff, vs))) // `v`.
            mstore(add(0x94, ptr), allowed)
            mstore(add(0x74, ptr), expiry)
            mstore(add(0x54, ptr), nonce)
            mstore(add(0x34, ptr), spender)
            mstore(add(0x20, ptr), shl(0x60, owner)) // with `spender`'s padding
            mstore(ptr, 0x8fcbaf0c000000000000000000000000) // selector for `permit(address,address,uint256,uint256,bool,uint8,bytes32,bytes32)`

            success := call(gas(), token, 0x00, add(0x10, ptr), 0x104, 0x00, 0x20)
            success := and(success, and(iszero(xor(mload(0x00), 0x01)), gt(returndatasize(), 0x1f)))
        }
    }

    function fastApproveMetaTransaction(
        IERC20MetaTransaction token,
        address owner,
        address spender,
        uint256 amount,
        bytes32 vs,
        bytes32 r
    ) internal returns (bool success, bytes32 functionSignatureHash) {
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(add(0xf8, ptr), amount)
            mstore(add(0xd8, ptr), spender)
            mstore(add(0xc4, ptr), 0x095ea7b3000000000000000000000000) // selector for `approve(address,uint256)` with `spender` padding
            mstore(add(0xb4, ptr), 0x44) // length of approve call
            mstore(add(0x94, ptr), add(0x1b, shr(0xff, vs))) // `v`.
            mstore(add(0x74, ptr), and(0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, vs)) // `s`.
            mstore(add(0x54, ptr), r) // `r`.
            mstore(add(0x34, ptr), 0xa0) // offset to function signature
            mstore(add(0x14, ptr), owner)
            mstore(ptr, 0x0c53c51c000000000000000000000000) // selector for `executeMetaTransaction(address,bytes,bytes32,bytes32,uint8)` with `owner`'s padding

            functionSignatureHash := keccak256(add(0xd4, ptr), 0x44)

            success := call(gas(), token, 0x00, add(0x10, ptr), 0x108, 0x00, 0x60)
            success := and(success, and(iszero(xor(mload(0x40), 0x01)), gt(returndatasize(), 0x5f)))

            mstore(0x40, ptr)
        }
    }

    function fastDomainSeparator(IERC20 token, uint32 domainSeparatorSelector)
        internal
        view
        returns (bytes32 domainSeparator)
    {
        assembly ("memory-safe") {
            mstore(0x00, domainSeparatorSelector)
            if iszero(staticcall(gas(), token, 0x1c, 0x04, 0x00, 0x20)) {
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

    function fastNonce(IERC20 token, address owner, uint32 nonceSelector) internal view returns (uint256 nonce) {
        assembly ("memory-safe") {
            mstore(0x14, owner)
            mstore(0x00, shl(0x60, nonceSelector)) // with `owner`'s padding
            if iszero(staticcall(gas(), token, 0x10, 0x24, 0x00, 0x20)) {
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
            mstore(0x34, spender)
            mstore(0x20, shl(0x60, owner)) // with `spender`'s padding
            mstore(0x00, 0xdd62ed3e000000000000000000000000) // selector for `allowance(address,address)` with `spender`'s padding
            if iszero(staticcall(gas(), token, 0x10, 0x44, 0x00, 0x20)) {
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
    using FastLogic for bool;
    using FastPermit for IERC2612;
    using FastPermit for IDAIStylePermit;
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
        if ((nonce == 0).or(token.fastAllowance(owner, spender) != amount)) {
            _revert(0xb78cb0dd); // selector for `PermitFailed()`
        }
    }

    function _checkSignature(bytes32 signingHash, address owner, bytes32 vs, bytes32 r) internal view {
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(0x00, signingHash)
            mstore(0x20, add(0x1b, shr(0xff, vs))) // `v`.
            mstore(0x40, r) // `r`.
            mstore(0x60, and(0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, vs)) // `s`.
            let recovered := mload(staticcall(gas(), 0x01, 0x00, 0x80, 0x01, 0x20))
            if lt(returndatasize(), shl(0x60, xor(owner, recovered))) {
                mstore(0x00, 0x8baa579f) // selector for `InvalidSignature()`
                revert(0x1c, 0x04)
            }
            mstore(0x40, ptr)
            mstore(0x60, 0x00)
        }
    }

    function safePermit(
        IERC2612 token,
        address owner,
        address spender,
        uint256 amount,
        uint256 deadline,
        bytes32 vs,
        bytes32 r
    ) internal {
        // `permit` could succeed vacuously with no returndata if there's a fallback
        // function (e.g. WETH). `permit` could fail spuriously if it was
        // replayed/frontrun. Avoid these by manually verifying the effects and
        // signature. Insufficient gas griefing is defused by checking the effects.
        if (!token.fastPermit(owner, spender, amount, deadline, vs, r)) {
            // Check effects and signature
            if (block.timestamp > deadline) {
                _revert(0x1a15a3cc); // selector for `PermitExpired()`
            }
            uint256 nonce = token.fastNonce(owner, uint32(token.nonces.selector));
            _checkEffects(token, owner, spender, amount, nonce);
            unchecked {
                nonce--;
            }
            bytes32 domainSeparator = token.fastDomainSeparator(uint32(token.DOMAIN_SEPARATOR.selector));
            bytes32 typeHash = _PERMIT_TYPEHASH;
            bytes32 signingHash;
            assembly ("memory-safe") {
                let ptr := mload(0x40)
                mstore(ptr, 0x1901)
                mstore(add(0x20, ptr), domainSeparator)
                mstore(add(0x40, ptr), typeHash)
                mstore(add(0x60, ptr), owner)
                mstore(add(0x80, ptr), spender)
                mstore(add(0xa0, ptr), amount)
                mstore(add(0xc0, ptr), nonce)
                mstore(add(0xe0, ptr), deadline)
                mstore(add(0x40, ptr), keccak256(add(0x40, ptr), 0xc0))
                signingHash := keccak256(add(0x1e, ptr), 0x42)
            }
            _checkSignature(signingHash, owner, vs, r);
        }
    }

    function safePermit(
        IDAIStylePermit token,
        address owner,
        address spender,
        uint256 nonce,
        uint256 deadline,
        bool allowed,
        bytes32 vs,
        bytes32 r
    ) internal {
        // See comments above
        if (!token.fastDAIPermit(owner, spender, nonce, deadline, allowed, vs, r)) {
            // Check effects and signature
            // https://etherscan.io/token/0x6b175474e89094c44da98b954eedeac495271d0f#code#L188
            if ((block.timestamp > deadline).and(deadline > 0)) {
                _revert(0x1a15a3cc);
            }
            nonce = token.fastNonce(owner, uint32(token.nonces.selector));
            uint256 expectedAllowance;
            unchecked {
                expectedAllowance = 0 - allowed.toUint();
            }
            _checkEffects(token, owner, spender, expectedAllowance, nonce);
            unchecked {
                nonce--;
            }
            bytes32 domainSeparator = token.fastDomainSeparator(uint32(token.DOMAIN_SEPARATOR.selector));
            bytes32 typeHash = _PERMIT_ALLOWED_TYPEHASH;
            bytes32 signingHash;
            assembly ("memory-safe") {
                let ptr := mload(0x40)
                mstore(ptr, 0x1901)
                mstore(add(0x20, ptr), domainSeparator)
                mstore(add(0x40, ptr), typeHash)
                mstore(add(0x60, ptr), owner)
                mstore(add(0x80, ptr), spender)
                mstore(add(0xa0, ptr), nonce)
                mstore(add(0xc0, ptr), deadline)
                mstore(add(0xe0, ptr), allowed)
                mstore(add(0x40, ptr), keccak256(add(0x40, ptr), 0xc0))
                signingHash := keccak256(add(0x1e, ptr), 0x42)
            }
            _checkSignature(signingHash, owner, vs, r);
        }
    }

    function safePermit(
        IERC20MetaTransaction token,
        address owner,
        address spender,
        uint256 amount,
        bytes32 vs,
        bytes32 r
    ) internal {
        // See comments above
        (bool success, bytes32 functionSignatureHash) = token.fastApproveMetaTransaction(owner, spender, amount, vs, r);
        if (!success) {
            // Check effects and signature
            uint256 nonce = token.fastNonce(owner, uint32(token.getNonce.selector));
            _checkEffects(token, owner, spender, amount, nonce);
            unchecked {
                nonce--;
            }
            bytes32 domainSeparator = token.fastDomainSeparator(uint32(token.getDomainSeperator.selector));
            bytes32 typeHash = _META_TRANSACTION_TYPEHASH;
            bytes32 signingHash;
            assembly ("memory-safe") {
                let ptr := mload(0x40)
                mstore(ptr, 0x1901)
                mstore(add(0x20, ptr), domainSeparator)
                mstore(add(0x40, ptr), typeHash)
                mstore(add(0x60, ptr), nonce)
                mstore(add(0x80, ptr), owner)
                mstore(add(0xa0, ptr), functionSignatureHash)
                mstore(add(0x40, ptr), keccak256(add(0x40, ptr), 0x80))
                signingHash := keccak256(add(0x1e, ptr), 0x42)
            }
            _checkSignature(signingHash, owner, vs, r);
        }
    }
}

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
    ) internal returns (bool success, bytes memory returnData) {
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
            success := call(gas(), token, 0x00, add(0x1c, ptr), 0xe4, 0x00, 0x00)

            let size := returndatasize()
            mstore(ptr, size)
            returndatacopy(add(0x20, ptr), 0x00, size)
            returnData := ptr

            mstore(0x40, add(0x20, add(size, ptr)))
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
    ) internal returns (bool success, bytes memory returnData) {
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
            success := call(gas(), token, 0x00, add(0x1c, ptr), 0x104, 0x00, 0x00)

            let size := returndatasize()
            mstore(ptr, size)
            returndatacopy(add(0x20, ptr), 0x00, size)
            returnData := ptr

            mstore(0x40, add(0x20, add(size, ptr)))
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
    ) internal returns (bool success, bytes memory returnData, bytes32 functionSignatureHash) {
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

            success := call(gas(), token, 0x00, add(0x10, ptr), 0x108, 0x00, 0x00)

            let size := returndatasize()
            mstore(ptr, size)
            returndatacopy(add(0x20, ptr), 0x00, size)
            returnData := ptr

            mstore(0x40, add(0x20, add(size, ptr)))
        }
    }

    function fastDomainSeparator(IERC20 token, bytes4 domainSeparatorSelector)
        internal
        view
        returns (bool success, bytes memory domainSeparator)
    {
        assembly ("memory-safe") {
            mstore(0x00, domainSeparatorSelector)
            success := staticcall(gas(), token, 0x00, 0x04, 0x00, 0x20)

            domainSeparator := mload(0x40)
            let size := returndatasize()
            mstore(domainSeparator, size)
            returndatacopy(add(0x20, domainSeparator), 0x00, size)
            mstore(0x40, add(0x20, add(size, domainSeparator)))
        }
    }

    function fastNonce(IERC20 token, address owner, bytes4 nonceSelector)
        internal
        view
        returns (bool success, bytes memory nonce)
    {
        assembly ("memory-safe") {
            mstore(0x00, nonceSelector)
            mstore(0x04, and(0xffffffffffffffffffffffffffffffffffffffff, owner))
            success := staticcall(gas(), token, 0x00, 0x24, 0x00, 0x20)

            nonce := mload(0x40)
            let size := returndatasize()
            mstore(nonce, size)
            returndatacopy(add(0x20, nonce), 0x00, size)
            mstore(0x40, add(0x20, add(size, nonce)))
        }
    }
}

library SafePermit {
    using Revert for bytes;
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

    function _bubbleRevert(bool success, bytes memory returndata, string memory message) internal pure {
        if (success) {
            revert(message);
        }
        returndata._revert();
    }

    function _checkEffects(
        IERC20 token,
        address owner,
        address spender,
        uint256 amount,
        uint256 nonce,
        bool success,
        bytes memory returndata
    ) internal view {
        if (nonce == 0) {
            _bubbleRevert(success, returndata, "SafePermit: zero nonce");
        }
        if (token.allowance(owner, spender) != amount) {
            _bubbleRevert(success, returndata, "SafePermit: failed");
        }
    }

    function _getDomainSeparator(IERC20 token, bytes4 domainSeparatorSelector) internal view returns (bytes32) {
        (bool success, bytes memory domainSeparator) = token.fastDomainSeparator(domainSeparatorSelector);
        if (!success || domainSeparator.length != 32) {
            _bubbleRevert(success, domainSeparator, "SafePermit: domain separator");
        }
        return abi.decode(domainSeparator, (bytes32));
    }

    function _getNonce(IERC20 token, address owner, bytes4 nonceSelector) internal view returns (uint256) {
        (bool success, bytes memory nonce) = token.fastNonce(owner, nonceSelector);
        if (!success || nonce.length != 32) {
            _bubbleRevert(success, nonce, "SafePermit: nonce");
        }
        return abi.decode(nonce, (uint256));
    }

    function _checkSignature(
        IERC20 token,
        bytes4 domainSeparatorSelector,
        address owner,
        bytes32 structHash,
        uint8 v,
        bytes32 r,
        bytes32 s,
        bool success,
        bytes memory returndata
    ) internal view {
        bytes32 signingHash = keccak256(
            bytes.concat(bytes2("\x19\x01"), _getDomainSeparator(token, domainSeparatorSelector), structHash)
        );
        address recovered = ecrecover(signingHash, v, r, s);
        if (recovered == address(0)) {
            _bubbleRevert(success, returndata, "SafePermit: bad signature");
        }
        if (recovered != owner) {
            _bubbleRevert(success, returndata, "SafePermit: wrong signer");
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
        (bool success, bytes memory returndata) = token.fastPermit(owner, spender, amount, deadline, v, r, s);
        if (success && returndata.length > 0 && abi.decode(returndata, (bool))) {
            return;
        }

        // Check effects and signature
        uint256 nonce = _getNonce(token, owner, token.nonces.selector);
        if (block.timestamp > deadline) {
            _bubbleRevert(success, returndata, "SafePermit: expired");
        }
        _checkEffects(token, owner, spender, amount, nonce, success, returndata);
        unchecked {
            nonce--;
        }
        bytes32 structHash = keccak256(abi.encode(_PERMIT_TYPEHASH, owner, spender, amount, nonce, deadline));
        _checkSignature(token, token.DOMAIN_SEPARATOR.selector, owner, structHash, v, r, s, success, returndata);
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
        (bool success, bytes memory returndata) =
            token.fastPermitAllowed(owner, spender, nonce, deadline, allowed, v, r, s);
        if (success && returndata.length > 0 && abi.decode(returndata, (bool))) {
            return;
        }

        // Check effects and signature
        if (block.timestamp > deadline && deadline > 0) {
            _bubbleRevert(success, returndata, "SafePermit: expired");
        }
        nonce = _getNonce(token, owner, token.nonces.selector);
        _checkEffects(token, owner, spender, allowed ? type(uint256).max : 0, nonce, success, returndata);
        unchecked {
            nonce--;
        }
        bytes32 structHash = keccak256(abi.encode(_PERMIT_ALLOWED_TYPEHASH, owner, spender, nonce, deadline, allowed));
        _checkSignature(token, token.DOMAIN_SEPARATOR.selector, owner, structHash, v, r, s, success, returndata);
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
        (bool success, bytes memory returndata, bytes32 functionSignatureHash) =
            token.fastApproveMetaTransaction(owner, spender, amount, v, r, s);
        if (success && returndata.length > 0 && abi.decode(abi.decode(returndata, (bytes)), (bool))) {
            return;
        }

        // Check effects and signature
        uint256 nonce = _getNonce(token, owner, token.getNonce.selector);
        _checkEffects(token, owner, spender, amount, nonce, success, returndata);
        unchecked {
            nonce--;
        }
        bytes32 structHash = keccak256(abi.encode(_META_TRANSACTION_TYPEHASH, nonce, owner, functionSignatureHash));
        _checkSignature(token, token.getDomainSeparator.selector, owner, structHash, v, r, s, success, returndata);
    }
}

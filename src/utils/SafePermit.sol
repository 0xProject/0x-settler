// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.19;

import {IERC20PermitCommon, IERC2612, IERC20PermitAllowed} from "../interfaces/IERC2612.sol";
import {IERC20MetaTransaction} from "../interfaces/INativeMetaTransaction.sol";
import {Revert} from "./Revert.sol";

library SafePermit {
    using Revert for bytes;

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
        IERC20PermitCommon token,
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

    function _getDomainSeparator(IERC20PermitCommon token, bytes4 domainSeparatorSelector)
        internal
        view
        returns (bytes32)
    {
        (bool success, bytes memory domainSeparator) = address(token).staticcall(bytes.concat(domainSeparatorSelector));
        if (!success || domainSeparator.length != 32) {
            _bubbleRevert(success, domainSeparator, "SafePermit: domain separator");
        }
        return abi.decode(domainSeparator, (bytes32));
    }

    function _checkSignature(
        IERC20PermitCommon token,
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
        bytes4 domainSeparatorSelector,
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
        (bool success, bytes memory returndata) =
            address(token).call(abi.encodeCall(token.permit, (owner, spender, amount, deadline, v, r, s)));
        if (success && returndata.length > 0 && abi.decode(returndata, (bool))) {
            return;
        }

        // Check effects and signature
        uint256 nonce = token.nonces(owner);
        if (block.timestamp > deadline) {
            _bubbleRevert(success, returndata, "SafePermit: expired");
        }
        _checkEffects(token, owner, spender, amount, nonce, success, returndata);
        unchecked {
            nonce--;
        }
        bytes32 structHash = keccak256(abi.encode(_PERMIT_TYPEHASH, owner, spender, amount, nonce, deadline));
        _checkSignature(token, domainSeparatorSelector, owner, structHash, v, r, s, success, returndata);
    }

    function safePermit(
        IERC20PermitAllowed token,
        bytes4 domainSeparatorSelector,
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
            address(token).call(abi.encodeCall(token.permit, (owner, spender, nonce, deadline, allowed, v, r, s)));
        if (success && returndata.length > 0 && abi.decode(returndata, (bool))) {
            return;
        }

        // Check effects and signature
        nonce = token.nonces(owner);
        if (block.timestamp > deadline && deadline > 0) {
            _bubbleRevert(success, returndata, "SafePermit: expired");
        }
        _checkEffects(token, owner, spender, allowed ? type(uint256).max : 0, nonce, success, returndata);
        unchecked {
            nonce--;
        }
        bytes32 structHash = keccak256(abi.encode(_PERMIT_ALLOWED_TYPEHASH, owner, spender, nonce, deadline, allowed));
        _checkSignature(token, domainSeparatorSelector, owner, structHash, v, r, s, success, returndata);
    }

    function safePermit(
        IERC20MetaTransaction token,
        bytes4 domainSeparatorSelector,
        address owner,
        address spender,
        uint256 amount,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) internal {
        // See comments above
        bytes memory functionSignature = abi.encodeCall(token.approve, (spender, amount));
        (bool success, bytes memory returndata) =
            address(token).call(abi.encodeCall(token.executeMetaTransaction, (owner, functionSignature, r, s, v)));
        if (success && returndata.length > 0 && abi.decode(abi.decode(returndata, (bytes)), (bool))) {
            return;
        }

        // Check effects and signature
        uint256 nonce = token.nonces(owner);
        _checkEffects(token, owner, spender, amount, nonce, success, returndata);
        unchecked {
            nonce--;
        }
        bytes32 structHash =
            keccak256(abi.encode(_META_TRANSACTION_TYPEHASH, nonce, owner, keccak256(functionSignature)));
        _checkSignature(token, domainSeparatorSelector, owner, structHash, v, r, s, success, returndata);
    }
}

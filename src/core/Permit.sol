// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20PermitCommon, IERC2612, IDAIStylePermit} from "../interfaces/IERC2612.sol";
import {IERC20MetaTransaction, INativeMetaTransaction} from "../interfaces/INativeMetaTransaction.sol";
import {ALLOWANCE_HOLDER} from "../allowanceholder/IAllowanceHolder.sol";
import {SafePermit} from "../utils/SafePermit.sol";
import {revertConfusedDeputy} from "./SettlerErrors.sol";

contract Permit {
    using SafePermit for IERC2612;
    using SafePermit for IDAIStylePermit;
    using SafePermit for IERC20MetaTransaction;

    enum PermitType {
        ERC2612,
        DAIPermit,
        NativeMetaTransaction
    }

    function getPermitType(bytes memory permitData)
        internal
        pure
        returns (PermitType permitType, bytes memory permitParams)
    {
        assembly ("memory-safe") {
            let length := mload(permitData)
            permitType := shr(0xf8, mload(add(0x20, permitData)))
            permitParams := add(0x01, permitData)
            mstore(permitParams, sub(length, 0x01))
        }
    }

    function callPermit(address token, bytes memory permitData) internal {
        (address owner, uint256 amount, uint256 deadline, uint8 v, bytes32 r, bytes32 s) =
            abi.decode(permitData, (address, uint256, uint256, uint8, bytes32, bytes32));
        IERC2612(token).safePermit(owner, address(ALLOWANCE_HOLDER), amount, deadline, v, r, s);
    }

    function callDAIPermit(address token, bytes memory permitData) internal {
        (address owner, uint256 nonce, uint256 expiry, bool allowed, uint8 v, bytes32 r, bytes32 s) =
            abi.decode(permitData, (address, uint256, uint256, bool, uint8, bytes32, bytes32));
        IDAIStylePermit(token).safePermit(owner, address(ALLOWANCE_HOLDER), nonce, expiry, allowed, v, r, s);
    }

    function callNativeMetaTransaction(address token, bytes memory permitData) internal {
        (address owner, uint256 amount, uint8 v, bytes32 r, bytes32 s) =
            abi.decode(permitData, (address, uint256, uint8, bytes32, bytes32));
        IERC20MetaTransaction(token).safePermit(owner, address(ALLOWANCE_HOLDER), amount, v, r, s);
    }

    function _dispatchPermit(address token, bytes memory permitData) internal {
        PermitType permitType;
        (permitType, permitData) = getPermitType(permitData);
        _handlePermit(token, permitType, permitData);
    }

    function _handlePermit(address token, PermitType permitType, bytes memory permitData) internal virtual {
        if (permitType == PermitType.ERC2612) {
            callPermit(token, permitData);
        } else if (permitType == PermitType.DAIPermit) {
            callDAIPermit(token, permitData);
        } else {
            // NativeMetaTransaction is disabled by default
            // callNativeMetaTransaction(token, permitData);
            unsupportedPermitType();
        }
    }

    function unsupportedPermitType() internal pure {
        assembly ("memory-safe") {
            mstore(0x00, 0x01aa0452) // selector for `UnsupportedPermitType()`
            revert(0x1c, 0x04)
        }
    }
}

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

    function callPermit(address owner, address token, bytes memory permitData) internal {
        (uint256 amount, uint256 deadline, bytes32 vs, bytes32 r) =
            abi.decode(permitData, (uint256, uint256, bytes32, bytes32));
        IERC2612(token).safePermit(owner, address(ALLOWANCE_HOLDER), amount, deadline, vs, r);
    }

    function callDAIPermit(address owner, address token, bytes memory permitData) internal {
        (uint256 nonce, uint256 expiry, bool allowed, bytes32 vs, bytes32 r) =
            abi.decode(permitData, (uint256, uint256, bool, bytes32, bytes32));
        IDAIStylePermit(token).safePermit(owner, address(ALLOWANCE_HOLDER), nonce, expiry, allowed, vs, r);
    }

    function callNativeMetaTransaction(address owner, address token, bytes memory permitData) internal {
        (uint256 amount, bytes32 vs, bytes32 r) = abi.decode(permitData, (uint256, bytes32, bytes32));
        IERC20MetaTransaction(token).safePermit(owner, address(ALLOWANCE_HOLDER), amount, vs, r);
    }

    function _dispatchPermit(address owner, address token, bytes memory permitData) internal {
        PermitType permitType;
        (permitType, permitData) = getPermitType(permitData);
        _handlePermit(owner, token, permitType, permitData);
    }

    function _handlePermit(address owner, address token, PermitType permitType, bytes memory permitData)
        internal
        virtual
    {
        if (permitType == PermitType.ERC2612) {
            callPermit(owner, token, permitData);
        } else if (permitType == PermitType.DAIPermit) {
            callDAIPermit(owner, token, permitData);
        } else {
            // NativeMetaTransaction is disabled by default
            // callNativeMetaTransaction(owner, token, permitData);
            unsupportedPermitType(permitType);
        }
    }

    function unsupportedPermitType(PermitType permitType) internal pure {
        assembly ("memory-safe") {
            let castError := gt(permitType, 0x02)
            mstore(0x00, xor(0xf9ade075, mul(0xb7e59b04, castError))) // selector for `UnsupportedPermitType(uint8)` or `Panic(uint256)`
            mstore(0x20, xor(permitType, mul(xor(permitType, 0x21), castError)))
            revert(0x1c, 0x24)
        }
    }
}

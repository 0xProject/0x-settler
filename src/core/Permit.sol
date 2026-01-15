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

    function callPermit(IERC2612 token, bytes memory permitData) internal {
        (address owner, uint256 amount, uint256 deadline, uint8 v, bytes32 r, bytes32 s) =
            abi.decode(permitData, (address, uint256, uint256, uint8, bytes32, bytes32));
        token.safePermit(owner, address(ALLOWANCE_HOLDER), amount, deadline, v, r, s);
    }

    function callDAIPermit(IDAIStylePermit token, bytes memory permitData) internal {
        (address owner, uint256 nonce, uint256 expiry, bool allowed, uint8 v, bytes32 r, bytes32 s) =
            abi.decode(permitData, (address, uint256, uint256, bool, uint8, bytes32, bytes32));
        token.safePermit(owner, address(ALLOWANCE_HOLDER), nonce, expiry, allowed, v, r, s);
    }

    function callNativeMetaTransaction(IERC20MetaTransaction token, bytes memory permitData) internal {
        (address owner, uint256 amount, uint8 v, bytes32 r, bytes32 s) =
            abi.decode(permitData, (address, uint256, uint8, bytes32, bytes32));
        token.safePermit(owner, address(ALLOWANCE_HOLDER), amount, v, r, s);
    }
}

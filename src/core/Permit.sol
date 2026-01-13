// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20PermitCommon, IERC2612, IERC20PermitAllowed} from "../interfaces/IERC2612.sol";
import {IERC20MetaTransaction, INativeMetaTransaction} from "../interfaces/INativeMetaTransaction.sol";
import {ALLOWANCE_HOLDER} from "../allowanceholder/IAllowanceHolder.sol";
import {SafePermit} from "../utils/SafePermit.sol";
import {revertConfusedDeputy} from "./SettlerErrors.sol";

contract Permit {
    using SafePermit for IERC2612;
    using SafePermit for IERC20PermitAllowed;
    using SafePermit for IERC20MetaTransaction;

    function callPermit(address token, bytes memory permitData) internal {
        uint32 permitSelector;
        bytes4 domainSeparatorSelector;
        assembly ("memory-safe") {
            let length := mload(permitData)
            let data := mload(add(0x20, permitData))
            // slice off the first 4 bytes of `permitData` as the permit selector
            permitSelector := shr(0xe0, data)
            // slice off another 4 bytes of `permitData` as the domain separator selector
            domainSeparatorSelector := shl(0xe0, shr(0xc0, data))
            // remove the selectors from the `permitData`
            permitData := add(0x08, permitData)
            mstore(permitData, sub(length, 0x08))
        }
        address spender = address(ALLOWANCE_HOLDER);
        if (permitSelector == uint32(IERC2612.permit.selector)) {
            (address owner, uint256 amount, uint256 deadline, uint8 v, bytes32 r, bytes32 s) =
                abi.decode(permitData, (address, uint256, uint256, uint8, bytes32, bytes32));
            IERC2612(token).safePermit(domainSeparatorSelector, owner, spender, amount, deadline, v, r, s);
        } else if (permitSelector == uint32(IERC20PermitAllowed.permit.selector)) {
            (address owner, uint256 nonce, uint256 expiry, bool allowed, uint8 v, bytes32 r, bytes32 s) =
                abi.decode(permitData, (address, uint256, uint256, bool, uint8, bytes32, bytes32));
            IERC20PermitAllowed(token)
                .safePermit(domainSeparatorSelector, owner, spender, nonce, expiry, allowed, v, r, s);
        } else if (permitSelector == uint32(INativeMetaTransaction.executeMetaTransaction.selector)) {
            (address owner, uint256 amount, uint8 v, bytes32 r, bytes32 s) =
                abi.decode(permitData, (address, uint256, uint8, bytes32, bytes32));
            IERC20MetaTransaction(token).safePermit(domainSeparatorSelector, owner, spender, amount, v, r, s);
        } else {
            revertConfusedDeputy();
        }
    }
}

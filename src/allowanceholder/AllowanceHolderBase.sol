// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IAllowanceHolder} from "./IAllowanceHolder.sol";
import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib_Solmate.sol";
import {CheckCall} from "../utils/CheckCall.sol";
import {FreeMemory} from "../utils/FreeMemory.sol";
import {TransientStorageLayout} from "./TransientStorageLayout.sol";

/// @notice Thrown when validating the target, avoiding executing against an ERC20 directly
error ConfusedDeputy();

abstract contract AllowanceHolderBase is TransientStorageLayout, FreeMemory {
    using SafeTransferLib for IERC20;
    using CheckCall for address payable;

    function _rejectIfERC20(address payable maybeERC20, bytes calldata data) private view DANGEROUS_freeMemory {
        // We could just choose a random address for this check, but to make
        // confused deputy attacks harder for tokens that might be badly behaved
        // (e.g. tokens with blacklists), we choose to copy the first argument
        // out of `data` and mask it as an address. If there isn't enough
        // `data`, we use 0xdead instead.
        address target;
        if (data.length > 0x10) {
            target = address(uint160(bytes20(data[0x10:])));
        }
        // EIP-1352 (not adopted) specifies 0xffff as the maximum precompile
        if (target <= address(0xffff)) {
            // 0xdead is a conventional burn address; we assume that it is not treated specially
            target = address(0xdead);
        }
        bytes memory testData = abi.encodeCall(IERC20.balanceOf, target);
        if (maybeERC20.checkCall(testData, 0x20)) revert ConfusedDeputy();
    }

    function _msgSender() private view returns (address sender) {
        if ((sender = msg.sender) == address(this)) {
            assembly ("memory-safe") {
                sender := shr(0x60, calldataload(sub(calldatasize(), 0x14)))
            }
        }
    }

    /// @dev This virtual function provides the implementation for the function
    ///      of the same name in `IAllowanceHolder`. It is unimplemented in this
    ///      base contract to accommodate the customization required to support
    ///      both chains that have EIP-1153 (transient storage) and those that
    ///      don't.
    function exec(address operator, address token, uint256 amount, address payable target, bytes calldata data)
        internal
        virtual
        returns (bytes memory result);

    /// @dev This is the majority of the implementation of IAllowanceHolder.exec
    ///      . The arguments have the same meaning as documented there.
    /// @return result
    /// @return sender The (possibly forwarded) message sender that is
    ///                requesting the allowance be set. Provided to avoid
    ///                duplicated computation in customized `exec`
    /// @return allowance The slot where the ephemeral allowance is
    ///                   stored. Provided to avoid duplicated computation in
    ///                   customized `exec`
    function _exec(address operator, address token, uint256 amount, address payable target, bytes calldata data)
        internal
        returns (bytes memory result, address sender, TSlot allowance)
    {
        // This contract has no special privileges, except for the allowances it
        // holds. In order to prevent abusing those allowances, we prohibit
        // sending arbitrary calldata (doing `target.call(data)`) to any
        // contract that might be an ERC20.
        _rejectIfERC20(target, data);

        sender = _msgSender();
        allowance = _ephemeralAllowance(operator, sender, token);
        _set(allowance, amount);

        // For gas efficiency we're omitting a bunch of checks here. Notably,
        // we're omitting the check that `address(this)` has sufficient value to
        // send (we know it does), and we're omitting the check that `target`
        // contains code (we already checked in `_rejectIfERC20`).
        assembly ("memory-safe") {
            result := mload(0x40)
            calldatacopy(result, data.offset, data.length)
            // ERC-2771 style msgSender forwarding https://eips.ethereum.org/EIPS/eip-2771
            mstore(add(result, data.length), shl(0x60, sender))
            let success := call(gas(), target, callvalue(), result, add(data.length, 0x14), 0x00, 0x00)
            let ptr := add(result, 0x20)
            returndatacopy(ptr, 0x00, returndatasize())
            switch success
            case 0 { revert(ptr, returndatasize()) }
            default {
                mstore(result, returndatasize())
                mstore(0x40, add(ptr, returndatasize()))
            }
        }
    }

    /// @dev This provides the implementation of the function of the same name
    ///      in `IAllowanceHolder`.
    function transferFrom(address token, address owner, address recipient, uint256 amount) internal {
        // msg.sender is the assumed and later validated operator
        TSlot allowance = _ephemeralAllowance(msg.sender, owner, token);
        // validation of the ephemeral allowance for operator, owner, token via
        // uint underflow
        _set(allowance, _get(allowance) - amount);
        // `safeTransferFrom` does not check that `token` actually contains
        // code. It is the responsibility of integrating code to check for that
        // if vacuous success is a security concern.
        IERC20(token).safeTransferFrom(owner, recipient, amount);
    }

    fallback() external payable {
        uint256 selector;
        assembly ("memory-safe") {
            selector := shr(0xe0, calldataload(0x00))
        }
        if (selector == uint256(uint32(IAllowanceHolder.transferFrom.selector))) {
            address token;
            address owner;
            address recipient;
            uint256 amount;
            assembly ("memory-safe") {
                // We do not validate `calldatasize()`. If the calldata is short
                // enough that `amount` is null, this call is a harmless no-op.
                let err := callvalue()
                token := calldataload(0x04)
                err := or(err, shr(0xa0, token))
                owner := calldataload(0x24)
                err := or(err, shr(0xa0, owner))
                recipient := calldataload(0x44)
                err := or(err, shr(0xa0, recipient))
                if err { revert(0x00, 0x00) }
                amount := calldataload(0x64)
            }

            transferFrom(token, owner, recipient, amount);

            // return true;
            assembly ("memory-safe") {
                mstore(0x00, 0x01)
                return(0x00, 0x20)
            }
        } else if (selector == uint256(uint32(IAllowanceHolder.exec.selector))) {
            address operator;
            address token;
            uint256 amount;
            address payable target;
            bytes calldata data;
            assembly ("memory-safe") {
                // We do not validate `calldatasize()`. If the calldata is short
                // enough that `data` is null, it will alias `operator`. This
                // results in either an OOG (because `operator` encodes a
                // too-long `bytes`) or is a harmless no-op (because `operator`
                // encodes a valid length, but not an address capable of making
                // calls). If the calldata is _so_ sort that `target` is null,
                // we will revert because it contains no code.
                operator := calldataload(0x04)
                let err := shr(0xa0, operator)
                token := calldataload(0x24)
                err := or(err, shr(0xa0, token))
                amount := calldataload(0x44)
                target := calldataload(0x64)
                err := or(err, shr(0xa0, target))
                if err { revert(0x00, 0x00) }
                // We perform no validation that `data` is reasonable.
                data.offset := add(0x04, calldataload(0x84))
                data.length := calldataload(data.offset)
                data.offset := add(0x20, data.offset)
            }

            bytes memory result = exec(operator, token, amount, target, data);

            // return result;
            assembly ("memory-safe") {
                let returndata := sub(result, 0x20)
                mstore(returndata, 0x20)
                return(returndata, add(0x40, mload(result)))
            }
        } else if (selector == uint256(uint32(IERC20.balanceOf.selector))) {
            // balanceOf(address) reverts with a single byte of returndata,
            // making it more gas efficient to pass the `_rejectERC20` check
            assembly ("memory-safe") {
                revert(0x00, 0x01)
            }
        } else {
            // emulate standard Solidity behavior
            assembly ("memory-safe") {
                revert(0x00, 0x00)
            }
        }
    }
}

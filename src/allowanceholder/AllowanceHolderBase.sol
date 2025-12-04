// SPDX-License-Identifier: MIT
pragma solidity =0.8.28;

import {IAllowanceHolder} from "./IAllowanceHolder.sol";
import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {CheckCall} from "../utils/CheckCall.sol";
import {FreeMemory} from "../utils/FreeMemory.sol";
import {Panic} from "../utils/Panic.sol";
import {Ternary} from "../utils/Ternary.sol";
import {TransientStorageLayout} from "./TransientStorageLayout.sol";

/// @notice Thrown when validating the target, avoiding executing against an ERC20 directly
error ConfusedDeputy();

abstract contract AllowanceHolderBase is TransientStorageLayout, FreeMemory {
    using SafeTransferLib for IERC20;
    using CheckCall for address payable;
    using Ternary for bool;

    address internal constant _MULTICALL = 0x00000000000000CF9E3c5A26621af382fA17f24f;

    constructor() {
        assert(
            (msg.sender == 0x4e59b44847b379578588920cA78FbF26c0B4956C && uint160(address(this)) >> 104 == 0)
                || block.chainid == 31337
        );
    }

    function _rejectIfERC20(address payable maybeERC20, bytes calldata data) private view DANGEROUS_freeMemory {
        // We could just choose a random address for this check, but to make
        // confused deputy attacks harder for tokens that might be badly behaved
        // (e.g. tokens with blacklists), we choose to copy the first argument
        // out of `data` and mask it as an address. If there isn't enough
        // `data`, we use 0xdead instead.

        address target; // = address(uint160(bytes20(data[0x10:])));
        assembly ("memory-safe") {
            target := calldataload(add(0x04, data.offset))
            // `shl(0x08, data.length)` can't overflow because we're going to
            // `calldatacopy(..., data.length)` later. It would OOG. We check
            // for underflow in `sub(data.length, 0x04)` later.
            let mask := shr(shl(0x08, sub(data.length, 0x04)), not(0x00))
            // Zero the low bits of `target` if `data` is short. Dirty low bits
            // are only ever possible with nonstandard encodings, like ERC-2771.
            target := and(not(mask), target)
            // Zero `target` if `sub(data.length, 0x04)` underflowed.
            target := mul(lt(0x03, data.length), target)
        }

        // EIP-1352 (not adopted) specifies 0xffff as the maximum precompile.
        // 0xdead is a conventional burn address; we assume that it is not
        // treated specially.
        target = (target > address(0xffff)).ternary(target, address(0xdead));

        bytes memory testData; // = abi.encodeCall(IERC20.balanceOf, target);
        assembly ("memory-safe") {
            testData := mload(0x40)
            mstore(add(0x24, testData), target)
            mstore(add(0x10, testData), 0x70a08231000000000000000000000000) // `IERC20.balanceOf.selector` with `target`'s padding
            mstore(testData, 0x24)
            mstore(0x40, add(0x60, testData))
        }

        if (maybeERC20.checkCall(testData, 0x20)) {
            assembly ("memory-safe") {
                mstore(0x00, 0xe758b8d5) // Selector for `ConfusedDeputy()`
                revert(0x1c, 0x04)
            }
        }
    }

    function _msgSender() private view returns (address sender) {
        assembly ("memory-safe") {
            let isSelfForwarded := eq(caller(), address())
            let isMultiCallForwarded := and(lt(0x03, calldatasize()), eq(_MULTICALL, caller()))
            sender :=
                xor(
                    caller(),
                    mul(
                        xor(caller(), shr(0x60, calldataload(sub(calldatasize(), 0x14)))),
                        or(isMultiCallForwarded, isSelfForwarded)
                    )
                )
        }
    }

    /// @dev This function provides the implementation for the function of the
    ///      same name in `IAllowanceHolder`. The arguments and return value
    ///      have the same meaning as documented there.
    function exec(address operator, address token, uint256 amount, address payable target, bytes calldata data)
        private
        returns (bytes memory result)
    {
        // This contract has no special privileges, except for the allowances it
        // holds. In order to prevent abusing those allowances, we prohibit
        // sending arbitrary calldata (doing `target.call(data)`) to any
        // contract that might be an ERC20.
        _rejectIfERC20(target, data);

        address sender = _msgSender();
        TSlot allowanceSlot = _ephemeralAllowance(operator, sender, token);
        _set(allowanceSlot, amount);

        // For gas efficiency we're omitting a bunch of checks here. Notably,
        // we're omitting the check that `address(this)` has sufficient value to
        // send (we know it does), and we're omitting the check that `target`
        // contains code (we already checked in `_rejectIfERC20`).
        assembly ("memory-safe") {
            // Copy the payload from calldata into memory
            result := mload(0x40)
            calldatacopy(result, data.offset, data.length)

            // ERC-2771 style `msgSender` forwarding https://eips.ethereum.org/EIPS/eip-2771
            // We do not append the forwarded sender if the payload has no selector
            mstore(add(result, data.length), shl(0x60, sender))
            let length := add(mul(0x14, lt(0x03, data.length)), data.length)

            // Perform the call
            let success := call(gas(), target, callvalue(), result, length, 0x00, 0x00)

            // Copy returndata into memory; if it is a revert, bubble
            let ptr := add(0x20, result)
            returndatacopy(ptr, 0x00, returndatasize())
            switch success
            case 0 { revert(ptr, returndatasize()) }
            default {
                // Wrap the returndata in a level of ABIEncoding
                mstore(result, returndatasize())
                mstore(0x40, add(returndatasize(), ptr))
            }
        }

        _set(allowanceSlot, 0);
    }

    /// @dev This provides the implementation of the function of the same name
    ///      in `IAllowanceHolder`. The arguments have the same meaning as
    ///      documented there.
    function transferFrom(address token, address owner, address recipient, uint256 amount) private {
        // `msg.sender` is the assumed and later validated `operator`.
        TSlot allowanceSlot = _ephemeralAllowance(msg.sender, owner, token);
        uint256 allowanceValue = _get(allowanceSlot);

        // We validate the ephemeral allowance for the 3-tuple of `operator`
        // (`msg.sender`), `owner`, and `token` by reverting on unsigned integer
        // underflow.
        if (allowanceValue < amount) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }

        // Update the ephemeral allowance
        unchecked {
            _set(allowanceSlot, allowanceValue - amount);
        }

        // `safeTransferFrom` does not check that `token` actually contains
        // code. It is the responsibility of integrating code to check for that,
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

            // `return true;`
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

            // `return result;`
            assembly ("memory-safe") {
                let returndata := sub(result, 0x20)
                // This is technically not "memory-safe", but manual examination
                // of the compiled bytecode shows that it's OK.
                mstore(returndata, 0x20)

                // Pad `returndata` to a multiple of 32 bytes.
                let len := mload(result)
                let m := and(0x1f, len)
                if m {
                    mstore(add(add(0x20, result), len), 0x00)
                    len := add(sub(0x20, m), len)
                }

                // Return the ABIEncoding of `result`.
                return(returndata, add(0x40, len))
            }
        } else if (selector == uint256(uint32(IERC20.balanceOf.selector))) {
            // `balanceOf(address)` returns a single byte of returndata, making
            // it more gas efficient to pass the `_rejectERC20` check during
            // recursive/reentrant calls.
            assembly ("memory-safe") {
                return(0x00, 0x01)
            }
        } else {
            // Emulate standard Solidity behavior.
            assembly ("memory-safe") {
                revert(0x00, 0x00)
            }
        }
    }
}

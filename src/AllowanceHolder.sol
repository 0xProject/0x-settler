// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {IAllowanceHolder} from "./IAllowanceHolder.sol";
import {IERC20} from "./IERC20.sol";
import {SafeTransferLib} from "./utils/SafeTransferLib.sol";
import {CheckCall} from "./utils/CheckCall.sol";
import {FreeMemory} from "./utils/FreeMemory.sol";

/// @notice Thrown when validating the target, avoiding executing against an ERC20 directly
error ConfusedDeputy();

library TransientStorage {
    struct TSlot {
        uint256 value;
    }

    function set(TSlot storage ts, uint256 nv) internal {
        assembly ("memory-safe") {
            sstore(ts.slot, nv) // will be `tstore` after Dencun (EIP-1153)
        }
    }

    function get(TSlot storage ts) internal view returns (uint256 cv) {
        assembly ("memory-safe") {
            cv := sload(ts.slot) // will be `tload` after Dencun (EIP-1153)
        }
    }
}

abstract contract TransientStorageMock {
    using TransientStorage for TransientStorage.TSlot;

    bytes32 private _sentinel;

    constructor() {
        uint256 _sentinelSlot;
        assembly ("memory-safe") {
            _sentinelSlot := _sentinel.slot
        }
        assert(_sentinelSlot == 0);
    }

    /// @dev The key for this ephemeral allowance is keccak256(abi.encodePacked(operator, owner, token)).
    function _ephemeralAllowance(address operator, address owner, address token)
        internal
        pure
        returns (TransientStorage.TSlot storage r)
    {
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(0x00, shl(0x60, operator))
            mstore(0x14, shl(0x60, owner)) // store owner at 0x14
            mstore(0x28, shl(0x60, token)) // store token at 0x28
            // allowance slot is keccak256(abi.encodePacked(operator, owner, token))
            r.slot := keccak256(0x00, 0x3c)
            // restore dirtied free pointer
            mstore(0x40, ptr)
        }
    }

    function _getAllowed(address operator, address owner, address token) internal view returns (uint256 r) {
        return _ephemeralAllowance(operator, owner, token).get();
    }

    function _setAllowed(address operator, address owner, address token, uint256 allowed) internal {
        _ephemeralAllowance(operator, owner, token).set(allowed);
    }
}

contract AllowanceHolder is TransientStorageMock, FreeMemory, IAllowanceHolder {
    using SafeTransferLib for IERC20;
    using CheckCall for address payable;
    using TransientStorage for TransientStorage.TSlot;

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
        if (target == address(0)) {
            target = address(0xdead);
        }
        bytes memory testData = abi.encodeCall(IERC20(maybeERC20).balanceOf, target);
        // 500k gas seems like a pretty healthy upper bound for the amount of
        // gas that `balanceOf` could reasonably consume in a well-behaved
        // ERC20.
        if (maybeERC20.checkCall(testData, 500_000, 0x20)) revert ConfusedDeputy();
    }

    function _msgSender() private view returns (address sender) {
        sender = msg.sender;
        if (sender == address(this)) {
            assembly ("memory-safe") {
                sender := shr(0x60, calldataload(sub(calldatasize(), 0x14)))
            }
        }
    }

    function balanceOf(address) external pure {
        assembly ("memory-safe") {
            mstore8(0x00, 0x00)
            revert(0x00, 0x01)
        }
    }

    /// @inheritdoc IAllowanceHolder
    function execute(address operator, address token, uint256 amount, address payable target, bytes calldata data)
        public
        payable
        override
        returns (bytes memory result)
    {
        // This contract has no special privileges, except for the allowances it
        // holds. In order to prevent abusing those allowances, we prohibit
        // sending arbitrary calldata (doing `target.call(data)`) to any
        // contract that might be an ERC20.
        _rejectIfERC20(target, data);

        address sender = _msgSender();
        _setAllowed(operator, sender, token, amount);

        // For gas efficiency we're omitting a bunch of checks here. Notably,
        // we're omitting the check that `address(this)` has sufficient value to
        // send (we know it does), and we're omitting the check that `target`
        // contains code (we already checked in `_rejectIfERC20`).
        assembly ("memory-safe") {
            result := mload(0x40)
            calldatacopy(result, data.offset, data.length)
            // ERC-2771 style msgSender forwarding https://eips.ethereum.org/EIPS/eip-2771
            mstore(add(result, data.length), shl(0x60, sender))
            let success :=
                call(
                    gas(),
                    and(0xffffffffffffffffffffffffffffffffffffffff, target),
                    callvalue(),
                    result,
                    add(data.length, 0x14),
                    0x00,
                    0x00
                )
            let ptr := add(result, 0x20)
            returndatacopy(ptr, 0x00, returndatasize())
            switch success
            case 0 { revert(ptr, returndatasize()) }
            default {
                mstore(result, returndatasize())
                mstore(0x40, add(ptr, returndatasize()))
            }
        }

        // EIP-3074 seems unlikely
        if (sender != tx.origin) {
            _setAllowed(operator, sender, token, 0);
        }
    }

    /// @inheritdoc IAllowanceHolder
    function holderTransferFrom(address token, address owner, address recipient, uint256 amount)
        public
        override
        returns (bool)
    {
        // msg.sender is the assumed and later validated operator
        TransientStorage.TSlot storage allowance = _ephemeralAllowance(msg.sender, owner, token);
        // validation of the ephemeral allowance for operator, owner, token via uint underflow
        allowance.set(allowance.get() - amount);
        IERC20(token).safeTransferFrom(owner, recipient, amount);
        return true;
    }

    function ephemeralAllowance(address operator, address owner, address token)
        external
        view
        override
        returns (uint256)
    {
        return _getAllowed(operator, owner, token);
    }

    // This is here as a deploy-time check that AllowanceHolder doesn't have any
    // state. If it did, it would interfere with TransientStorageMock. This can
    // be removed once *actual* EIP-1153 is adopted.
    bytes32 private _sentinel;

    constructor() {
        uint256 _sentinelSlot;
        assembly ("memory-safe") {
            _sentinelSlot := _sentinel.slot
        }
        assert(_sentinelSlot == 1);
    }
}

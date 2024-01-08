// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {IAllowanceHolder} from "./IAllowanceHolder.sol";
import {IERC20} from "./IERC20.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {SafeTransferLib} from "./vendor/SafeTransferLib.sol";
import {UnsafeMath} from "./utils/UnsafeMath.sol";
import {CheckCall} from "./utils/CheckCall.sol";
import {FreeMemory} from "./utils/FreeMemory.sol";

/// @notice Thrown when validating the target, avoiding executing against an ERC20 directly
error ConfusedDeputy();

library UnsafeArray {
    function unsafeGet(ISignatureTransfer.TokenPermissions[] calldata a, uint256 i)
        internal
        pure
        returns (ISignatureTransfer.TokenPermissions calldata r)
    {
        assembly ("memory-safe") {
            r := add(a.offset, shl(6, i))
        }
    }

    function unsafeGet(IAllowanceHolder.TransferDetails[] calldata a, uint256 i)
        internal
        pure
        returns (IAllowanceHolder.TransferDetails calldata r)
    {
        assembly ("memory-safe") {
            r := add(a.offset, mul(0x60, i))
        }
    }
}

abstract contract TransientStorageMock {
    bytes32 private _sentinel;

    constructor() {
        uint256 _sentinelSlot;
        assembly ("memory-safe") {
            _sentinelSlot := _sentinel.slot
        }
        assert(_sentinelSlot == 0);
    }

    /// @dev The key for this ephemeral allowance is keccak256(abi.encodePacked(operator, owner, token)).
    /// Later authorisation for this is validated through the presence of this key being set
    function _getAllowed(address operator, address owner, address token) internal view returns (uint256 r) {
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(0x00, shl(0x60, operator))
            mstore(0x14, shl(0x60, owner)) // store owner at 0x14
            mstore(0x28, shl(0x60, token)) // store token at 0x28
            // allowance slot is keccak256(abi.encodePacked(operator, owner, token))
            r := sload(keccak256(0x00, 0x3c))
            mstore(0x40, ptr)
        }
    }

    function _setAllowed(address operator, address owner, address token, uint256 allowed) internal {
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(0x00, shl(0x60, operator))
            mstore(0x14, shl(0x60, owner)) // store owner at 0x14
            mstore(0x28, shl(0x60, token)) // store token at 0x28
            // allowance slot is keccak256(abi.encodePacked(operator, owner, token))
            sstore(keccak256(0x00, 0x3c), allowed)
            mstore(0x40, ptr)
        }
    }
}

contract AllowanceHolder is TransientStorageMock, FreeMemory, IAllowanceHolder {
    using SafeTransferLib for IERC20;
    using CheckCall for address payable;
    using UnsafeMath for uint256;
    using UnsafeArray for ISignatureTransfer.TokenPermissions[];
    using UnsafeArray for TransferDetails[];

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

    /// @inheritdoc IAllowanceHolder
    function execute(
        address operator,
        ISignatureTransfer.TokenPermissions[] calldata permits,
        address payable target,
        bytes calldata data
    ) public payable override returns (bytes memory result) {
        // This contract has no special privileges, except for the allowances it
        // holds. In order to prevent abusing those allowances, we prohibit
        // sending arbitrary calldata (doing `target.call(data)`) to any
        // contract that might be an ERC20.
        _rejectIfERC20(target, data);

        for (uint256 i; i < permits.length; i = i.unsafeInc()) {
            ISignatureTransfer.TokenPermissions calldata permit = permits.unsafeGet(i);
            _setAllowed(operator, msg.sender, permit.token, permit.amount);
        }

        // For gas efficiency we're omitting a bunch of checks here. Notably,
        // we're omitting the check that `address(this)` has sufficient value to
        // send (we know it does), and we're omitting the check that `target`
        // contains code (we already checked in `_rejectIfERC20`).
        assembly ("memory-safe") {
            result := mload(0x40)
            calldatacopy(result, data.offset, data.length)
            // ERC-2771 style msgSender forwarding https://eips.ethereum.org/EIPS/eip-2771
            mstore(add(result, data.length), shl(0x60, caller()))
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

        for (uint256 i; i < permits.length; i = i.unsafeInc()) {
            _setAllowed(operator, msg.sender, permits.unsafeGet(i).token, 0);
        }
    }

    /// @inheritdoc IAllowanceHolder
    function holderTransferFrom(address owner, TransferDetails[] calldata transferDetails)
        public
        override
        returns (bool)
    {
        // msg.sender is the assumed and later verified operator
        for (uint256 i; i < transferDetails.length; i = i.unsafeInc()) {
            TransferDetails calldata transferDetail = transferDetails.unsafeGet(i);
            // validation of the ephemeral allowance for operator, owner, token via uint underflow
            _setAllowed(
                msg.sender,
                owner,
                transferDetail.token,
                _getAllowed(msg.sender, owner, transferDetail.token) - transferDetail.amount
            );
        }
        for (uint256 i; i < transferDetails.length; i = i.unsafeInc()) {
            TransferDetails calldata transferDetail = transferDetails.unsafeGet(i);
            IERC20(transferDetail.token).safeTransferFrom(owner, transferDetail.recipient, transferDetail.amount);
        }
        return true;
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

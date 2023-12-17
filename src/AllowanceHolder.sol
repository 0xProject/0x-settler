// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {IAllowanceHolder} from "./IAllowanceHolder.sol";
import {IERC20} from "./IERC20.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {SafeTransferLib} from "./utils/SafeTransferLib.sol";
import {UnsafeMath} from "./utils/UnsafeMath.sol";
import {CheckCall} from "./utils/CheckCall.sol";
import {FreeMemory} from "./utils/FreeMemory.sol";
import {Revert} from "./utils/Revert.sol";

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
        _setOperator(address(1)); // this is the address of a precompile, but it doesn't matter
    }

    // this emulates transient storage while solc doesn't support it. there's no
    // reason to use a mapping here because this contract has only 2 things it
    // needs to store.
    uint256 private constant _ADDRESS_MASK = 0x00ffffffffffffffffffffffffffffffffffffffff;
    uint256 private constant _OPERATOR_SLOT = 0x010000000000000000000000000000000000000000;

    function _getAllowed(address token) internal view returns (uint256 r) {
        assembly ("memory-safe") {
            r := sload(and(_ADDRESS_MASK, token))
        }
    }

    function _setAllowed(address token, uint256 allowed) internal {
        assembly ("memory-safe") {
            sstore(and(_ADDRESS_MASK, token), allowed)
        }
    }

    function _getOperator() internal view returns (address r) {
        assembly ("memory-safe") {
            r := sload(_OPERATOR_SLOT)
        }
    }

    function _setOperator(address operator) internal {
        assembly ("memory-safe") {
            sstore(_OPERATOR_SLOT, and(_ADDRESS_MASK, operator))
        }
    }
}

contract AllowanceHolder is TransientStorageMock, FreeMemory, IAllowanceHolder {
    using SafeTransferLib for IERC20;
    using CheckCall for address payable;
    using UnsafeMath for uint256;
    using UnsafeArray for ISignatureTransfer.TokenPermissions[];
    using UnsafeArray for TransferDetails[];
    using Revert for bool;

    error ConfusedDeputy();

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
        if (maybeERC20.checkCall(testData, 500_000, 0x20)) {
            revert ConfusedDeputy();
        }
    }

    /// @inheritdoc IAllowanceHolder
    function execute(
        address operator,
        ISignatureTransfer.TokenPermissions[] calldata permits,
        address payable target,
        bytes calldata data
    ) public payable override returns (bytes memory result) {
        require(msg.sender == tx.origin); // caller is an EOA; effectively a reentrancy guard; EIP-3074 seems unlikely
        // This contract has no special privileges, except for the allowances it
        // holds. In order to prevent abusing those allowances, we prohibit
        // sending arbitrary calldata (doing `target.call(data)`) to any
        // contract that might be an ERC20.
        _rejectIfERC20(target, data);

        _setOperator(operator);
        for (uint256 i; i < permits.length; i = i.unsafeInc()) {
            ISignatureTransfer.TokenPermissions calldata permit = permits.unsafeGet(i);
            _setAllowed(permit.token, permit.amount);
        }

        {
            bool success;
            // ERC-2771 style msgSender forwarding https://eips.ethereum.org/EIPS/eip-2771
            (success, result) = target.call{value: msg.value}(abi.encodePacked(data, tx.origin));
            success.maybeRevert(result);
        }

        // this isn't required after *actual* EIP-1153 is adopted. this is only needed for the mock
        _setOperator(address(1)); // this is the address of a precompile, but it doesn't matter
        for (uint256 i; i < permits.length; i = i.unsafeInc()) {
            _setAllowed(permits.unsafeGet(i).token, 0);
        }
    }

    function _checkAmountsAndTransfer(TransferDetails[] calldata transferDetails) private {
        for (uint256 i; i < transferDetails.length; i = i.unsafeInc()) {
            TransferDetails calldata transferDetail = transferDetails.unsafeGet(i);
            _setAllowed(transferDetail.token, _getAllowed(transferDetail.token) - transferDetail.amount); // reverts on underflow
        }
        for (uint256 i; i < transferDetails.length; i = i.unsafeInc()) {
            TransferDetails calldata transferDetail = transferDetails.unsafeGet(i);
            IERC20(transferDetail.token).safeTransferFrom(tx.origin, transferDetail.recipient, transferDetail.amount);
        }
    }

    /// @inheritdoc IAllowanceHolder
    function holderTransferFrom(address owner, TransferDetails[] calldata transferDetails)
        public
        override
        returns (bool)
    {
        assert(owner == tx.origin);
        require(msg.sender == _getOperator());
        _checkAmountsAndTransfer(transferDetails);
        return true;
    }

    /// @inheritdoc IAllowanceHolder
    function moveExecute(
        ISignatureTransfer.TokenPermissions[] calldata permits,
        address payable target,
        bytes calldata data
    ) public payable override returns (bytes memory result) {
        // This contract has no special privileges, except for the allowances it
        // holds. In order to prevent abusing those allowances, we prohibit
        // sending arbitrary calldata (doing `target.call(data)`) to any
        // contract that might be an ERC20.
        _rejectIfERC20(target, data);

        // Move all funds into `target`
        for (uint256 i; i < permits.length; i = i.unsafeInc()) {
            ISignatureTransfer.TokenPermissions calldata permit = permits.unsafeGet(i);
            IERC20(permit.token).safeTransferFrom(msg.sender, target, permit.amount);
        }

        {
            bool success;
            // ERC-2771 style msgSender forwarding https://eips.ethereum.org/EIPS/eip-2771
            (success, result) = target.call{value: msg.value}(abi.encodePacked(data, msg.sender));
            success.maybeRevert(result);
        }
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

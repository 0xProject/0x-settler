// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {ERC20} from "solmate/src/tokens/ERC20.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {SafeTransferLib} from "./utils/SafeTransferLib.sol";

contract AllowanceHolder {
    using SafeTransferLib for ERC20;

    bytes32 internal constant _MOCK_TRANSIENT_START_SLOT =
        0x588fe8b62ed655cf29d31d5107e62b4fbc51f24e11339fa0f890fb831d2e43bb;

    constructor() {
        assert(_MOCK_TRANSIENT_START_SLOT == bytes32(uint256(keccak256("mock transient start slot")) - 1));
    }

    struct MockTransientStorage {
        address from;
        address to;
        ISignatureTransfer.TokenPermissions[] permitted;
    }

    function _storePermits(address from, address to, ISignatureTransfer.TokenPermissions[] calldata permitted)
        internal
    {
        MockTransientStorage storage dst;
        assembly ("memory-safe") {
            dst.slot := _MOCK_TRANSIENT_START_SLOT
        }
        dst.from = from;
        dst.to = to;
        dst.permitted = permitted;
    }

    function _getPermits()
        internal
        view
        returns (address from, address to, ISignatureTransfer.TokenPermissions[] memory permitted)
    {
        MockTransientStorage storage src;
        assembly ("memory-safe") {
            src.slot := _MOCK_TRANSIENT_START_SLOT
        }
        return (src.from, src.to, src.permitted);
    }

    function _clearPermits() internal {
        MockTransientStorage storage dst;
        assembly ("memory-safe") {
            dst.slot := _MOCK_TRANSIENT_START_SLOT
        }
        delete dst.from;
        delete dst.to;
        delete dst.permitted;
    }

    function execute(
        address to,
        ISignatureTransfer.TokenPermissions[] calldata permitted,
        address payable target,
        bytes calldata data
    ) public payable returns (bytes memory) {
        require(msg.sender == tx.origin); // caller is an EOA; effectively a reentrancy guard
        _storePermits(msg.sender, to, permitted);
        (bool success, bytes memory returndata) =
            target.call{value: msg.value}(bytes.concat(data, bytes20(uint160(msg.sender))));
        if (!success) {
            assembly ("memory-safe") {
                revert(add(returndata, 0x20), mload(returndata))
            }
        }
        _clearPermits();
        return returndata;
    }

    function transferFrom(ISignatureTransfer.SignatureTransferDetails[] calldata transferDetails, address owner)
        public
    {
        (address from, address to, ISignatureTransfer.TokenPermissions[] memory permitted) = _getPermits();
        require(msg.sender == to);
        require(from == owner);
        _clearPermits(); // this is effectively a reentrancy guard
        for (uint256 i; i < permitted.length; i++) {
            ISignatureTransfer.TokenPermissions memory permit = permitted[i];
            ISignatureTransfer.SignatureTransferDetails memory detail = transferDetails[i];
            uint256 amount = detail.requestedAmount;
            require(amount <= permit.amount);
            if (amount != 0) {
                ERC20(permit.token).safeTransferFrom(from, detail.to, amount);
            }
        }
    }
}

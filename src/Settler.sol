// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ISettlerTakerSubmitted} from "./interfaces/ISettlerTakerSubmitted.sol";

import {Permit2PaymentTakerSubmitted} from "./core/Permit2Payment.sol";
import {Permit2PaymentAbstract} from "./core/Permit2PaymentAbstract.sol";

import {AbstractContext} from "./Context.sol";
import {CalldataDecoder, SettlerBase} from "./SettlerBase.sol";
import {UnsafeMath} from "./utils/UnsafeMath.sol";

import {ISettlerActions} from "./ISettlerActions.sol";
import {revertActionInvalid, SignatureExpired, MsgValueMismatch} from "./core/SettlerErrors.sol";
import {CalldataBytesIterator, LibCalldataBytesIterator} from "./utils/Iterators.sol";

// ugh; solidity inheritance
import {SettlerAbstract} from "./SettlerAbstract.sol";

abstract contract Settler is ISettlerTakerSubmitted, Permit2PaymentTakerSubmitted, SettlerBase {
    using UnsafeMath for uint256;
    using CalldataDecoder for bytes[];
    using LibCalldataBytesIterator for bytes[];
    using LibCalldataBytesIterator for CalldataBytesIterator;

    function _tokenId() internal pure override returns (uint256) {
        return 2;
    }

    function _hasMetaTxn() internal pure override returns (bool) {
        return false;
    }

    function _dispatch(uint256 i, uint256 action, bytes calldata data)
        internal
        virtual
        override(SettlerAbstract, SettlerBase)
        returns (bool)
    {
        if (super._dispatch(i, action, data)) {
            return true;
        } else if (action == uint32(ISettlerActions.NATIVE_CHECK.selector)) {
            (uint256 deadline, uint256 msgValue) = abi.decode(data, (uint256, uint256));
            if (block.timestamp > deadline) {
                assembly ("memory-safe") {
                    mstore(0x00, 0xcd21db4f) // selector for `SignatureExpired(uint256)`
                    mstore(0x20, deadline)
                    revert(0x1c, 0x24)
                }
            }
            if (msg.value > msgValue) {
                assembly ("memory-safe") {
                    mstore(0x00, 0x4a094431) // selector for `MsgValueMismatch(uint256,uint256)`
                    mstore(0x20, msgValue)
                    mstore(0x40, callvalue())
                    revert(0x1c, 0x44)
                }
            }
        } else {
            return false;
        }
        return true;
    }

    function _dispatchVIP(uint256 action, bytes calldata data) internal virtual returns (bool) {
        if (action == uint32(ISettlerActions.TRANSFER_FROM.selector)) {
            (address recipient, ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) =
                abi.decode(data, (address, ISignatureTransfer.PermitTransferFrom, bytes));
            (ISignatureTransfer.SignatureTransferDetails memory transferDetails,) =
                _permitToTransferDetails(permit, recipient);
            _transferFrom(permit, transferDetails, sig);
        } /*
        // RFQ_VIP is temporarily removed because Solver has no support for it
        // When support for RFQ_VIP is reenabled, the tests
        // testAllowanceHolder_rfq_VIP and testSettler_rfq should be reenabled
        else if (action == uint32(ISettlerActions.RFQ_VIP.selector)) {
            (
                address recipient,
                ISignatureTransfer.PermitTransferFrom memory makerPermit,
                address maker,
                bytes memory makerSig,
                ISignatureTransfer.PermitTransferFrom memory takerPermit,
                bytes memory takerSig
            ) = abi.decode(
                data,
                (
                    address,
                    ISignatureTransfer.PermitTransferFrom,
                    address,
                    bytes,
                    ISignatureTransfer.PermitTransferFrom,
                    bytes
                )
            );
            fillRfqOrderVIP(recipient, makerPermit, maker, makerSig, takerPermit, takerSig);
        } */ else if (action == uint32(ISettlerActions.UNISWAPV3_VIP.selector)) {
            (
                address recipient,
                bytes memory path,
                ISignatureTransfer.PermitTransferFrom memory permit,
                bytes memory sig,
                uint256 amountOutMin
            ) = abi.decode(data, (address, bytes, ISignatureTransfer.PermitTransferFrom, bytes, uint256));

            sellToUniswapV3VIP(recipient, path, permit, sig, amountOutMin);
        } else {
            return false;
        }
        return true;
    }

    function execute(AllowedSlippage calldata slippage, bytes[] calldata actions, bytes32 /* zid & affiliate */ )
        public
        payable
        override
        takerSubmitted
        returns (bool)
    {
        if (actions.length != 0) {
            CalldataBytesIterator it = actions.iter();
            {
                (uint256 action, bytes calldata data) = actions.decodeCall(it);
                if (!_dispatchVIP(action, data)) {
                    if (!_dispatch(0, action, data)) {
                        revertActionInvalid(0, action, data);
                    }
                }
            }
            it = it.next();
            for (uint256 i = 1; i < actions.length; (i, it) = (i.unsafeInc(), it.next())) {
                (uint256 action, bytes calldata data) = actions.decodeCall(it);
                if (!_dispatch(i, action, data)) {
                    revertActionInvalid(i, action, data);
                }
            }
        }

        _checkSlippageAndTransfer(slippage);
        return true;
    }

    // Solidity inheritance is stupid
    function _msgSender()
        internal
        view
        virtual
        override(Permit2PaymentTakerSubmitted, AbstractContext)
        returns (address)
    {
        return super._msgSender();
    }

    function _isRestrictedTarget(address target)
        internal
        pure
        virtual
        override(Permit2PaymentTakerSubmitted, Permit2PaymentAbstract)
        returns (bool)
    {
        return super._isRestrictedTarget(target);
    }
}

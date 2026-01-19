// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ISettlerTakerSubmitted} from "./interfaces/ISettlerTakerSubmitted.sol";

import {Permit2PaymentTakerSubmitted} from "./core/Permit2Payment.sol";
import {Permit2PaymentAbstract} from "./core/Permit2PaymentAbstract.sol";
import {Permit} from "./core/Permit.sol";

import {AbstractContext} from "./Context.sol";
import {CalldataDecoder, SettlerBase} from "./SettlerBase.sol";
import {UnsafeMath} from "./utils/UnsafeMath.sol";

import {ISettlerActions} from "./ISettlerActions.sol";
import {revertActionInvalid, SignatureExpired, MsgValueMismatch, revertConfusedDeputy} from "./core/SettlerErrors.sol";
import {Revert} from "./utils/Revert.sol";

// ugh; solidity inheritance
import {SettlerAbstract} from "./SettlerAbstract.sol";
import {FastLogic} from "./utils/FastLogic.sol";

abstract contract Settler is ISettlerTakerSubmitted, Permit2PaymentTakerSubmitted, SettlerBase, Permit {
    using UnsafeMath for uint256;
    using CalldataDecoder for bytes[];
    using Revert for bool;
    using FastLogic for bool;

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
        //// NOTICE: Portions of this function have been copy/paste'd into
        //// `src/chains/Mainnet/TakerSubmitted.sol:MainnetSettler._dispatch`. If you make changes
        //// here, you need to make sure that corresponding changes are made to that function.

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
        //// NOTICE: Portions of this function have been copy/paste'd into
        //// `src/chains/Katana/TakerSubmitted.sol:KatanaSettler._dispatchVIP`. If you make changes
        //// here, you need to make sure that corresponding changes are made to that function.

        if (action == uint32(ISettlerActions.TRANSFER_FROM.selector)) {
            (address recipient, ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) =
                abi.decode(data, (address, ISignatureTransfer.PermitTransferFrom, bytes));
            (ISignatureTransfer.SignatureTransferDetails memory transferDetails,) =
                _permitToTransferDetails(permit, recipient);
            _transferFrom(permit, transferDetails, sig);
        } else if (action == uint32(ISettlerActions.TRANSFER_FROM_WITH_PERMIT.selector)) {
            (address recipient, ISignatureTransfer.PermitTransferFrom memory permit, bytes memory permitData) =
                abi.decode(data, (address, ISignatureTransfer.PermitTransferFrom, bytes));
            // permit.permitted.token should not be restricted, _isRestrictedTarget(permit.permitted.token) 
            // is not verified because the selectors of supported permit calls doesn't clash with any
            // selectors of existing restricted targets, namely, AllowanceHolder, Permit2 and Bebop
            if (!_isForwarded()) {
                revertConfusedDeputy();
            }
            _dispatchPermit(_msgSender(), permit.permitted.token, permitData);
            (ISignatureTransfer.SignatureTransferDetails memory transferDetails,) =
                _permitToTransferDetails(permit, recipient);
            _transferFrom(permit, transferDetails, new bytes(0), true);
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
            uint256 it;
            assembly ("memory-safe") {
                it := actions.offset
            }
            {
                (uint256 action, bytes calldata data) = actions.decodeCall(it);
                if (!_dispatchVIP(action, data)) {
                    if (!_dispatch(0, action, data)) {
                        revertActionInvalid(0, action, data);
                    }
                }
            }
            it = it.unsafeAdd(32);
            for (uint256 i = 1; i < actions.length; (i, it) = (i.unsafeInc(), it.unsafeAdd(32))) {
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
        view
        virtual
        override(Permit2PaymentTakerSubmitted, Permit2PaymentAbstract)
        returns (bool)
    {
        return super._isRestrictedTarget(target);
    }
}

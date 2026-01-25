// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ISettlerMetaTxn} from "./interfaces/ISettlerMetaTxn.sol";

import {Permit2PaymentAbstract} from "./core/Permit2PaymentAbstract.sol";
import {Permit2PaymentBase, Permit2PaymentMetaTxn} from "./core/Permit2Payment.sol";

import {Context, AbstractContext} from "./Context.sol";
import {CalldataDecoder, SettlerBase} from "./SettlerBase.sol";
import {UnsafeMath} from "./utils/UnsafeMath.sol";

import {ISettlerActions} from "./ISettlerActions.sol";
import {revertActionInvalid} from "./core/SettlerErrors.sol";

abstract contract SettlerMetaTxn is ISettlerMetaTxn, Permit2PaymentMetaTxn, SettlerBase {
    using UnsafeMath for uint256;
    using CalldataDecoder for bytes[];

    function _tokenId() internal pure virtual override returns (uint256) {
        return 3;
    }

    function _hasMetaTxn() internal pure override returns (bool) {
        return true;
    }

    function _hashArrayOfBytes(bytes[] calldata actions) internal pure returns (bytes32 result) {
        // This function deliberately does no bounds checking on `actions` for
        // gas efficiency. We assume that `actions` will get used elsewhere in
        // this context and any OOB or other malformed calldata will result in a
        // revert later.
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            let hashesLength := shl(0x05, actions.length)
            for {
                let i := actions.offset
                let dst := ptr
                let end := add(i, hashesLength)
            } lt(i, end) {
                i := add(0x20, i)
                dst := add(0x20, dst)
            } {
                let src := add(calldataload(i), actions.offset)
                let length := calldataload(src)
                calldatacopy(dst, add(0x20, src), length)
                mstore(dst, keccak256(dst, length))
            }
            result := keccak256(ptr, hashesLength)
        }
    }

    function _hashActionsAndSlippage(bytes[] calldata actions, AllowedSlippage calldata slippage)
        internal
        pure
        returns (bytes32 result)
    {
        // This function does not check for or clean any dirty bits that might
        // exist in `slippage`. We assume that `slippage` will be used elsewhere
        // in this context and that if there are dirty bits it will result in a
        // revert later.
        bytes32 arrayOfBytesHash = _hashArrayOfBytes(actions);
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(ptr, SLIPPAGE_AND_ACTIONS_TYPEHASH)
            calldatacopy(add(0x20, ptr), slippage, 0x60)
            mstore(add(0x80, ptr), arrayOfBytesHash)
            result := keccak256(ptr, 0xa0)
        }
    }

    function _dispatchVIP(uint256 action, bytes calldata data, bytes calldata sig) internal virtual returns (bool) {
        if (action == uint32(ISettlerActions.METATXN_TRANSFER_FROM.selector)) {
            (address recipient, ISignatureTransfer.PermitTransferFrom memory permit) =
                abi.decode(data, (address, ISignatureTransfer.PermitTransferFrom));
            (ISignatureTransfer.SignatureTransferDetails memory transferDetails,) =
                _permitToTransferDetails(permit, recipient);

            // We simultaneously transfer-in the taker's tokens and authenticate the
            // metatransaction.
            _transferFrom(permit, transferDetails, sig);
        } /*
        // METATXN_RFQ_VIP is temporarily removed because Solver has no support
        // for it. When support for METATXN_RFQ_VIP is reenabled, the test
        // testSettler_metaTxn_rfq should be reenabled
        else if (action == uint32(ISettlerActions.METATXN_RFQ_VIP.selector)) {
            // An optimized path involving a maker/taker in a single trade
            // The RFQ order is signed by both maker and taker, validation is
            // performed inside the RfqOrderSettlement so there is no need to
            // validate `sig` against `actions` here
            (
                address recipient,
                ISignatureTransfer.PermitTransferFrom memory makerPermit,
                address maker,
                bytes memory makerSig,
                ISignatureTransfer.PermitTransferFrom memory takerPermit
            ) = abi.decode(
                data,
                (address, ISignatureTransfer.PermitTransferFrom, address, bytes, ISignatureTransfer.PermitTransferFrom)
            );
            fillRfqOrderVIP(recipient, makerPermit, maker, makerSig, takerPermit, sig);
        } */ else if (action == uint32(ISettlerActions.METATXN_UNISWAPV3_VIP.selector)) {
            (
                address recipient,
                bytes memory path,
                ISignatureTransfer.PermitTransferFrom memory permit,
                uint256 amountOutMin
            ) = abi.decode(data, (address, bytes, ISignatureTransfer.PermitTransferFrom, uint256));

            sellToUniswapV3VIP(recipient, path, permit, sig, amountOutMin);
        } else {
            return false;
        }
        return true;
    }

    function _executeMetaTxn(AllowedSlippage calldata slippage, bytes[] calldata actions, bytes calldata sig)
        internal
        returns (bool)
    {
        require(actions.length != 0);
        uint256 it;
        assembly ("memory-safe") {
            it := actions.offset
        }
        {
            (uint256 action, bytes calldata data) = actions.decodeCall(it);

            // By forcing the first action to be one of the witness-aware
            // actions, we ensure that the entire sequence of actions is
            // authorized. `msgSender` is the signer of the metatransaction.
            if (!_dispatchVIP(action, data, sig)) {
                revertActionInvalid(0, action, data);
            }
        }
        it = it.unsafeAdd(32);
        for (uint256 i = 1; i < actions.length; (i, it) = (i.unsafeInc(), it.unsafeAdd(32))) {
            (uint256 action, bytes calldata data) = actions.decodeCall(it);
            if (!_dispatch(i, action, data)) {
                revertActionInvalid(i, action, data);
            }
        }

        _checkSlippageAndTransfer(slippage);
        return true;
    }

    function executeMetaTxn(
        AllowedSlippage calldata slippage,
        bytes[] calldata actions,
        bytes32 /* zid & affiliate */,
        address msgSender,
        bytes calldata sig
    ) public virtual override metaTx(msgSender, _hashActionsAndSlippage(actions, slippage)) returns (bool) {
        return _executeMetaTxn(slippage, actions, sig);
         emit MetaTxnExecuted(
        msgSender,                      // signer
        msg.sender,                     // relayer
        actions.length,
        _hashActionsAndSlippage(actions, slippage)
    );

    return ok;
    }

    // Solidity inheritance is stupid
    function _isRestrictedTarget(address target)
        internal
        view
        virtual
        override(Permit2PaymentAbstract, Permit2PaymentBase)
        returns (bool)
    {
        return super._isRestrictedTarget(target);
    }

    function _msgSender() internal view virtual override(Permit2PaymentMetaTxn, AbstractContext) returns (address) {
        return super._msgSender();
    }
}

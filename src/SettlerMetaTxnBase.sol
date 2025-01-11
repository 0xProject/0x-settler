// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";

import {Permit2PaymentMetaTxn} from "./core/Permit2Payment.sol";

import {Context, AbstractContext} from "./Context.sol";
import {CalldataDecoder, SettlerBase} from "./SettlerBase.sol";
import {UnsafeMath} from "./utils/UnsafeMath.sol";

import {ISettlerActions} from "./ISettlerActions.sol";
import {ConfusedDeputy, ActionInvalid} from "./core/SettlerErrors.sol";

abstract contract SettlerMetaTxnBase is Permit2PaymentMetaTxn, SettlerBase {
    using UnsafeMath for uint256;
    using CalldataDecoder for bytes[];

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
            let hashesLength := shl(5, actions.length)
            for {
                let i := actions.offset
                let dst := ptr
                let end := add(i, hashesLength)
            } lt(i, end) {
                i := add(i, 0x20)
                dst := add(dst, 0x20)
            } {
                let src := add(actions.offset, calldataload(i))
                let length := calldataload(src)
                calldatacopy(dst, add(src, 0x20), length)
                mstore(dst, keccak256(dst, length))
            }
            result := keccak256(ptr, hashesLength)
        }
    }

    function _hashSlippageAnd(bytes32 typehash, bytes[] calldata actions, AllowedSlippage calldata slippage)
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
            mstore(ptr, typehash)
            calldatacopy(add(ptr, 0x20), slippage, 0x60)
            mstore(add(ptr, 0x80), arrayOfBytesHash)
            result := keccak256(ptr, 0xa0)
        }
    }

    function _dispatchVIP(uint256 action, bytes calldata data, bytes calldata sig) internal virtual returns (bool) {
        if (action == uint32(ISettlerActions.METATXN_RFQ_VIP.selector)) {
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
        } else if (action == uint32(ISettlerActions.METATXN_TRANSFER_FROM.selector)) {
            (address recipient, ISignatureTransfer.PermitTransferFrom memory permit) =
                abi.decode(data, (address, ISignatureTransfer.PermitTransferFrom));
            (ISignatureTransfer.SignatureTransferDetails memory transferDetails,) =
                _permitToTransferDetails(permit, recipient);

            // We simultaneously transfer-in the taker's tokens and authenticate the
            // metatransaction.
            _transferFrom(permit, transferDetails, sig);
        } else if (action == uint32(ISettlerActions.METATXN_UNISWAPV3_VIP.selector)) {
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

    function _executeMetaTxn(
        AllowedSlippage calldata slippage,
        bytes[] calldata actions,
        bytes calldata sig,
        uint256 fundingActionIndex
    ) internal returns (bool) {
        require(actions.length > fundingActionIndex);

        uint256 i;
        for (; i < fundingActionIndex; i = i.unsafeInc()) {
            (uint256 action, bytes calldata data) = actions.decodeCall(i);
            if (!_dispatch(action, data)) {
                revert ActionInvalid(i, bytes4(uint32(action)), data);
            }
        }

        {
            (uint256 action, bytes calldata data) = actions.decodeCall(i);
            if (!_dispatchVIP(action, data, sig)) {
                revert ActionInvalid(i, bytes4(uint32(action)), data);
            }
        }

        i = i.unsafeInc();
        for (; i < actions.length; i = i.unsafeInc()) {
            (uint256 action, bytes calldata data) = actions.decodeCall(i);
            if (!_dispatch(action, data)) {
                revert ActionInvalid(i, bytes4(uint32(action)), data);
            }
        }

        _checkSlippageAndTransfer(slippage);
        return true;
    }
}

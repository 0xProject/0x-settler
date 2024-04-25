// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20, IERC20Meta} from "./IERC20.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";

import {CalldataDecoder, SettlerBase} from "./SettlerBase.sol";
import {UnsafeMath} from "./utils/UnsafeMath.sol";

import {ISettlerActions} from "./ISettlerActions.sol";

contract SettlerMetaTxn is SettlerBase {
    using UnsafeMath for uint256;
    using CalldataDecoder for bytes[];

    constructor(address uniFactory, address dai) SettlerBase(uniFactory, dai) {}

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
            mstore(ptr, ACTIONS_AND_SLIPPAGE_TYPEHASH)
            calldatacopy(add(ptr, 0x20), slippage, 0x60)
            mstore(add(ptr, 0x80), arrayOfBytesHash)
            result := keccak256(ptr, 0xa0)
        }
    }

    function _metaTxnOtcVIP(bytes calldata data, address msgSender, bytes calldata sig) internal DANGEROUS_freeMemory {
        // An optimized path involving a maker/taker in a single trade
        // The OTC order is signed by both maker and taker, validation is
        // performed inside the OtcOrderSettlement so there is no need to
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
        fillOtcOrderMetaTxn(recipient, makerPermit, maker, makerSig, takerPermit, msgSender, sig);
    }

    function _metaTxnTransferFrom(bytes calldata data, address msgSender, bytes calldata sig)
        internal
        DANGEROUS_freeMemory
    {
        (address recipient, ISignatureTransfer.PermitTransferFrom memory permit) =
            abi.decode(data, (address, ISignatureTransfer.PermitTransferFrom));
        (ISignatureTransfer.SignatureTransferDetails memory transferDetails,,) =
            _permitToTransferDetails(permit, recipient);

        // We simultaneously transfer-in the taker's tokens and authenticate the
        // metatransaction.
        _transferFrom(permit, transferDetails, msgSender, sig);
    }

    function _metaTxnUniV3VIP(bytes calldata data, address msgSender, bytes calldata sig)
        internal
        DANGEROUS_freeMemory
    {
        (
            address recipient,
            uint256 amountOutMin,
            bytes memory path,
            ISignatureTransfer.PermitTransferFrom memory permit
        ) = abi.decode(data, (address, uint256, bytes, ISignatureTransfer.PermitTransferFrom));
        sellToUniswapV3MetaTxn(recipient, path, amountOutMin, msgSender, permit, sig);
    }

    function _metaTxnCurveTricryptoVIP(bytes calldata data, address msgSender, bytes calldata sig)
        internal
        DANGEROUS_freeMemory
    {
        (address recipient, uint80 poolInfo, uint256 minBuyAmount, ISignatureTransfer.PermitTransferFrom memory permit)
        = abi.decode(data, (address, uint80, uint256, ISignatureTransfer.PermitTransferFrom));
        sellToCurveTricryptoMetaTxn(recipient, poolInfo, minBuyAmount, msgSender, permit, sig);
    }

    function _metaTxnSolidlyV3VIP(bytes calldata data, address msgSender, bytes calldata sig)
        internal
        DANGEROUS_freeMemory
    {
        (
            address recipient,
            uint256 amountOutMin,
            bytes memory path,
            ISignatureTransfer.PermitTransferFrom memory permit
        ) = abi.decode(data, (address, uint256, bytes, ISignatureTransfer.PermitTransferFrom));
        sellToSolidlyV3MetaTxn(recipient, path, amountOutMin, msgSender, permit, sig);
    }

    function executeMetaTxn(
        bytes[] calldata actions,
        AllowedSlippage calldata slippage,
        address msgSender,
        bytes calldata sig
    ) public metaTx(msgSender, _hashActionsAndSlippage(actions, slippage)) {
        if (actions.length != 0) {
            (bytes4 action, bytes calldata data) = actions.decodeCall(0);

            // By forcing the first action to be one of the witness-aware
            // actions, we ensure that the entire sequence of actions is
            // authorized. `msgSender` is the signer of the metatransaction.

            if (action == ISettlerActions.METATXN_OTC_VIP.selector) {
                _metaTxnOtcVIP(data, msgSender, sig);
            } else if (action == ISettlerActions.METATXN_TRANSFER_FROM.selector) {
                _metaTxnTransferFrom(data, msgSender, sig);
            } else if (action == ISettlerActions.METATXN_UNISWAPV3_VIP.selector) {
                _metaTxnUniV3VIP(data, msgSender, sig);
            } else if (action == ISettlerActions.METATXN_CURVE_TRICRYPTO_VIP.selector) {
                _metaTxnCurveTricryptoVIP(data, msgSender, sig);
            } else if (action == ISettlerActions.METATXN_SOLIDLYV3_VIP.selector) {
                _metaTxnSolidlyV3VIP(data, msgSender, sig);
            } else {
                revert ActionInvalid({i: 0, action: action, data: data});
            }
        }

        for (uint256 i = 1; i < actions.length; i = i.unsafeInc()) {
            (bytes4 action, bytes calldata data) = actions.decodeCall(i);
            _dispatch(i, action, data, msgSender);
        }

        _checkSlippageAndTransfer(slippage);
    }
}

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "../IERC20.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {SettlerAbstract} from "../SettlerAbstract.sol";

import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {FullMath} from "../vendor/FullMath.sol";

abstract contract OtcOrderSettlement is SettlerAbstract {
    using SafeTransferLib for IERC20;
    using FullMath for uint256;

    struct Consideration {
        address token;
        uint256 amount;
        address counterparty;
        bool partialFillAllowed;
    }

    string internal constant CONSIDERATION_TYPE =
        "Consideration(address token,uint256 amount,address counterparty,bool partialFillAllowed)";
    // `string.concat` isn't recognized by solc as compile-time constant, but `abi.encodePacked` is
    string internal constant CONSIDERATION_WITNESS =
        string(abi.encodePacked("Consideration consideration)", CONSIDERATION_TYPE, TOKEN_PERMISSIONS_TYPE));
    bytes32 internal constant CONSIDERATION_TYPEHASH =
        0x7d806873084f389a66fd0315dead7adaad8ae6e8b6cf9fb0d3db61e5a91c3ffa;

    string internal constant OTC_ORDER_TYPE =
        "OtcOrder(Consideration makerConsideration,Consideration takerConsideration)";
    string internal constant OTC_ORDER_TYPE_RECURSIVE = string(abi.encodePacked(OTC_ORDER_TYPE, CONSIDERATION_TYPE));
    bytes32 internal constant OTC_ORDER_TYPEHASH = 0x4efcac36537dd5721596376472101aec5ff380b23b286c66cdfe70a509c0cef3;

    function _hashConsideration(Consideration memory consideration) internal pure returns (bytes32 result) {
        assembly ("memory-safe") {
            let ptr := sub(consideration, 0x20)
            let oldValue := mload(ptr)
            mstore(ptr, CONSIDERATION_TYPEHASH)
            result := keccak256(ptr, 0xa0)
            mstore(ptr, oldValue)
        }
    }

    function _logOtcOrder(bytes32 makerConsiderationHash, bytes32 takerConsiderationHash, uint128 makerFilledAmount)
        private
    {
        assembly ("memory-safe") {
            mstore(0x00, OTC_ORDER_TYPEHASH)
            mstore(0x20, makerConsiderationHash)
            let ptr := mload(0x40)
            mstore(0x40, takerConsiderationHash)
            let orderHash := keccak256(0x00, 0x60)
            mstore(0x40, ptr)
            mstore(0x10, makerFilledAmount)
            mstore(0x00, orderHash)
            log0(0x00, 0x30)
        }
    }

    constructor() {
        assert(CONSIDERATION_TYPEHASH == keccak256(bytes(CONSIDERATION_TYPE)));
        assert(OTC_ORDER_TYPEHASH == keccak256(bytes(OTC_ORDER_TYPE_RECURSIVE)));
    }

    /// @dev Settle an OtcOrder between maker and taker transferring funds directly between
    /// the counterparties. Either two Permit2 signatures are consumed, with the maker Permit2 containing
    /// a witness of the OtcOrder, or AllowanceHolder is supported for the taker payment.
    function fillOtcOrder(
        address recipient,
        ISignatureTransfer.PermitTransferFrom memory makerPermit,
        address maker,
        bytes memory makerSig,
        ISignatureTransfer.PermitTransferFrom memory takerPermit,
        bytes memory takerSig
    ) internal {
        return fillOtcOrderMetaTxn(recipient, makerPermit, maker, makerSig, takerPermit, _msgSender(), takerSig);
    }

    /// @dev Settle an OtcOrder between maker and taker transfering funds directly between
    /// the counterparties. Both Maker and Taker have signed the same order, and submission
    /// is via a third party
    /// @dev the taker's witness is not calculated nor verified here as calling function is trusted
    function fillOtcOrderMetaTxn(
        address recipient,
        ISignatureTransfer.PermitTransferFrom memory makerPermit,
        address maker,
        bytes memory makerSig,
        ISignatureTransfer.PermitTransferFrom memory takerPermit,
        address taker,
        bytes memory takerSig
    ) internal {
        (
            ISignatureTransfer.SignatureTransferDetails memory makerTransferDetails,
            address makerToken,
            uint256 makerAmount
        ) = _permitToTransferDetails(makerPermit, recipient);
        (
            ISignatureTransfer.SignatureTransferDetails memory takerTransferDetails,
            address takerToken,
            uint256 takerAmount
        ) = _permitToTransferDetails(takerPermit, maker);

        bytes32 witness = _hashConsideration(
            Consideration({token: takerToken, amount: takerAmount, counterparty: taker, partialFillAllowed: false})
        );
        _transferFrom(takerPermit, takerTransferDetails, taker, takerSig);
        _transferFrom(makerPermit, makerTransferDetails, maker, witness, CONSIDERATION_WITNESS, makerSig, false);

        _logOtcOrder(
            witness,
            _hashConsideration(
                Consideration({token: makerToken, amount: makerAmount, counterparty: maker, partialFillAllowed: false})
            ),
            uint128(makerAmount)
        );
    }

    /// @dev Settle an OtcOrder between maker and Settler retaining funds in this contract.
    /// @dev pre-condition: msgSender has been authenticated against the requestor
    /// One Permit2 signature is consumed, with the maker Permit2 containing a witness of the OtcOrder.
    // In this variant, Maker pays recipient and Settler pays Maker
    function fillOtcOrderSelfFunded(
        address recipient,
        ISignatureTransfer.PermitTransferFrom memory permit,
        address maker,
        bytes memory makerSig,
        IERC20 takerToken,
        uint256 maxTakerAmount,
        address msgSender
    ) internal {
        // Compute witnesses. These are based on the quoted maximum amounts. We will modify them
        // later to adjust for the actual settled amount, which may be modified by encountered
        // slippage.
        (ISignatureTransfer.SignatureTransferDetails memory transferDetails, address makerToken, uint256 makerAmount) =
            _permitToTransferDetails(permit, recipient);
        bytes32 takerWitness = _hashConsideration(
            Consideration({token: makerToken, amount: makerAmount, counterparty: maker, partialFillAllowed: true})
        );
        bytes32 makerWitness = _hashConsideration(
            Consideration({
                token: address(takerToken),
                amount: maxTakerAmount,
                counterparty: msgSender,
                partialFillAllowed: true
            })
        );

        // Now we adjust the transfer amounts to compensate for encountered slippage. Rounding is
        // performed in the maker's favor.
        uint256 takerAmount = takerToken.balanceOf(address(this));
        if (takerAmount > maxTakerAmount) {
            takerAmount = maxTakerAmount;
        }
        transferDetails.requestedAmount = makerAmount = makerAmount.unsafeMulDiv(takerAmount, maxTakerAmount);

        // Now that we have all the relevant information, make the transfers and log the order.
        takerToken.safeTransfer(maker, takerAmount);
        _transferFrom(permit, transferDetails, maker, makerWitness, CONSIDERATION_WITNESS, makerSig, false);

        _logOtcOrder(makerWitness, takerWitness, uint128(makerAmount));
    }
}

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {ERC20} from "solmate/src/tokens/ERC20.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {SignatureTransferUser} from "./SignatureTransferUser.sol";

import {SafeTransferLib} from "../utils/SafeTransferLib.sol";

/// @dev An OtcOrder is a simplified and minimized order type. It can only be filled once and
/// has additional requirements for txOrigin
abstract contract OtcOrderSettlement is SignatureTransferUser {
    using SafeTransferLib for ERC20;

    struct OtcOrder {
        address makerToken;
        address takerToken;
        uint128 makerAmount;
        uint128 takerAmount;
        address maker;
        address taker;
        address txOrigin;
    }

    /// @dev Emitted whenever an `OtcOrder` is filled.
    /// @param orderHash The canonical hash of the order.
    /// @param maker The maker of the order.
    /// @param taker The taker of the order.
    /// @param makerTokenFilledAmount How much maker token was filled.
    /// @param takerTokenFilledAmount How much taker token was filled.
    event OtcOrderFilled(
        bytes32 orderHash,
        address maker,
        address taker,
        address makerToken,
        address takerToken,
        uint128 makerTokenFilledAmount,
        uint128 takerTokenFilledAmount
    );

    string internal constant OTC_ORDER_TYPE =
        "OtcOrder(address makerToken,address takerToken,uint128 makerAmount,uint128 takerAmount,address maker,address taker,address txOrigin)";
    // `string.concat` isn't recognized by solc as compile-time constant, but `abi.encodePacked` is
    string internal constant OTC_ORDER_WITNESS =
        string(abi.encodePacked("OtcOrder order)", OTC_ORDER_TYPE, TOKEN_PERMISSIONS_TYPE_STRING));
    bytes32 internal constant OTC_ORDER_TYPEHASH = 0xfb940004397cdd921b9c6d5f56542c06432403925e8ad3894ddec13430dfbb1a;

    string internal constant TAKER_METATXN_OTC_ORDER_TYPE = "TakerMetatxnOtcOrder(OtcOrder order,address recipient)";
    string internal constant TAKER_METATXN_OTC_ORDER_TYPE_RECURSIVE =
        string(abi.encodePacked(TAKER_METATXN_OTC_ORDER_TYPE, OTC_ORDER_TYPE));
    string internal constant TAKER_METATXN_OTC_ORDER_WITNESS = string(
        abi.encodePacked(
            "TakerMetatxnOtcOrder order)", OTC_ORDER_TYPE, TAKER_METATXN_OTC_ORDER_TYPE, TOKEN_PERMISSIONS_TYPE
        )
    );
    bytes32 internal constant TAKER_METATXN_OTC_ORDER_TYPEHASH =
        0xbf00b5db6c90b28592de57c30ed48371a001917709d9d55056481b8b1673b118;

    function _hashOtcOrder(OtcOrder memory otcOrder) internal pure returns (bytes32 result) {
        assembly ("memory-safe") {
            let ptr := sub(otcOrder, 0x20)
            let oldValue := mload(ptr)
            mstore(ptr, OTC_ORDER_TYPEHASH)
            result := keccak256(ptr, 0x100)
            mstore(ptr, oldValue)
        }
    }

    function _hashTakerMetatxnOtcOrder(OtcOrder memory otcOrder, address recipient)
        internal
        pure
        returns (bytes32 result)
    {
        result = _hashOtcOrder(otcOrder);
        assembly ("memory-safe") {
            mstore(0x00, TAKER_METATXN_OTC_ORDER_TYPEHASH)
            mstore(0x20, result)
            let ptr := mload(0x40)
            mstore(0x40, recipient)
            result := keccak256(0x00, 0x60)
            mstore(0x40, ptr)
        }
    }

    ISignatureTransfer private immutable PERMIT2;

    constructor(address permit2) {
        PERMIT2 = ISignatureTransfer(permit2);
        assert(OTC_ORDER_TYPEHASH == keccak256(bytes(OTC_ORDER_TYPE)));
        assert(TAKER_METATXN_OTC_ORDER_TYPEHASH == keccak256(bytes(TAKER_METATXN_OTC_ORDER_TYPE_RECURSIVE)));
    }

    /// @dev Settle an OtcOrder between maker and taker transfering funds directly between
    /// the counterparties. Two Permit2 signatures are consumed, with the maker Permit2 containing
    /// a witness of the OtcOrder.
    function fillOtcOrder(
        OtcOrder memory order,
        ISignatureTransfer.PermitTransferFrom memory makerPermit,
        bytes memory makerSig,
        ISignatureTransfer.PermitTransferFrom memory takerPermit,
        bytes memory takerSig,
        address taker,
        uint128 takerTokenFillAmount,
        address recipient
    ) internal returns (uint128 takerTokenFilledAmount, uint128 makerTokenFilledAmount) {
        // TODO validate order.taker and taker
        // TODO validate tx.origin and txOrigin
        // TODO adjust amounts based on takerTokenFillAmount

        // Maker pays recipient
        ISignatureTransfer.SignatureTransferDetails memory makerToRecipientTransferDetails =
            ISignatureTransfer.SignatureTransferDetails({to: recipient, requestedAmount: order.makerAmount});
        bytes32 witness = _hashOtcOrder(order);
        PERMIT2.permitWitnessTransferFrom(
            makerPermit, makerToRecipientTransferDetails, order.maker, witness, OTC_ORDER_WITNESS, makerSig
        );

        // Taker pays Maker
        ISignatureTransfer.SignatureTransferDetails memory takerToMakerTransferDetails =
            ISignatureTransfer.SignatureTransferDetails({to: order.maker, requestedAmount: order.takerAmount});
        PERMIT2.permitTransferFrom(takerPermit, takerToMakerTransferDetails, taker, takerSig);

        // TODO actually calculate the orderHash
        emit OtcOrderFilled(
            witness, order.maker, taker, order.makerToken, order.takerToken, order.makerAmount, order.takerAmount
        );
    }

    /// @dev Settle an OtcOrder between maker and taker transfering funds directly between
    /// the counterparties. Two Permit2 signatures are consumed, with the maker Permit2 containing
    /// a witness of the OtcOrder.
    /// This variant also includes a fee where the taker or maker pays the fee recipient
    function fillOtcOrder(
        OtcOrder memory order,
        ISignatureTransfer.PermitBatchTransferFrom memory makerPermit,
        bytes memory makerSig,
        ISignatureTransfer.PermitBatchTransferFrom memory takerPermit,
        bytes memory takerSig,
        address taker,
        uint128 takerTokenFillAmount,
        address recipient
    ) internal returns (uint128 takerTokenFilledAmount, uint128 makerTokenFilledAmount) {
        // TODO validate order.taker and taker
        // TODO validate tx.origin and txOrigin
        // TODO adjust amounts based on takerTokenFillAmount

        require(makerPermit.permitted.length <= 2, "Invalid Batch Permit2");
        require(takerPermit.permitted.length <= 2, "Invalid Batch Permit2");

        // Maker pays out recipient and optional fee to fee recipient
        ISignatureTransfer.SignatureTransferDetails[] memory makerTransferDetails =
            new ISignatureTransfer.SignatureTransferDetails[](makerPermit.permitted.length);
        makerTransferDetails[0] =
            ISignatureTransfer.SignatureTransferDetails({to: recipient, requestedAmount: order.makerAmount});
        if (makerPermit.permitted.length > 1) {
            // TODO fee recipient
            makerTransferDetails[1] = ISignatureTransfer.SignatureTransferDetails({
                to: 0x2222222222222222222222222222222222222222,
                requestedAmount: makerPermit.permitted[1].amount
            });
            // adjust the maker->recipient payout by the fee amount
            makerTransferDetails[0].requestedAmount -= makerPermit.permitted[1].amount;
        }

        bytes32 witness = _hashOtcOrder(order);
        PERMIT2.permitWitnessTransferFrom(
            makerPermit, makerTransferDetails, order.maker, witness, OTC_ORDER_WITNESS, makerSig
        );

        // Taker pays Maker and optional fee to fee recipient
        ISignatureTransfer.SignatureTransferDetails[] memory takerTransferDetails =
            new ISignatureTransfer.SignatureTransferDetails[](takerPermit.permitted.length);
        takerTransferDetails[0] =
            ISignatureTransfer.SignatureTransferDetails({to: order.maker, requestedAmount: order.takerAmount});
        if (takerPermit.permitted.length > 1) {
            // TODO fee recipient
            takerTransferDetails[1] = ISignatureTransfer.SignatureTransferDetails({
                to: 0x2222222222222222222222222222222222222222,
                requestedAmount: takerPermit.permitted[1].amount
            });
            // No adjustment in payout of taker->maker, maker always receives full amount
        }
        PERMIT2.permitTransferFrom(takerPermit, takerTransferDetails, taker, takerSig);

        // TODO actually calculate the orderHash
        emit OtcOrderFilled(
            witness, order.maker, taker, order.makerToken, order.takerToken, order.makerAmount, order.takerAmount
        );
    }

    /// @dev Settle an OtcOrder between maker and taker transfering funds directly between
    /// the counterparties. Both Maker and Taker have signed the same order, and submission
    /// is via a third party
    function fillOtcOrderMetaTxn(
        OtcOrder memory order,
        ISignatureTransfer.PermitBatchTransferFrom memory makerPermit,
        bytes memory makerSig,
        ISignatureTransfer.PermitBatchTransferFrom memory takerPermit,
        bytes memory takerSig,
        address recipient
    ) internal returns (uint128 takerTokenFilledAmount, uint128 makerTokenFilledAmount) {
        // TODO validate tx.origin and txOrigin

        // TODO: allow multiple fees
        require(makerPermit.permitted.length <= 2, "Invalid Batch Permit2");
        require(takerPermit.permitted.length <= 2, "Invalid Batch Permit2");

        // Pay close attention to the order in which these operations are
        // performed. It's very important for security and the implications are not
        // intuitive.

        // Maker pays Taker (optional fee)
        bytes32 witness = _hashOtcOrder(order);
        ISignatureTransfer.SignatureTransferDetails[] memory makerTransferDetails =
            new ISignatureTransfer.SignatureTransferDetails[](makerPermit.permitted.length);
        if (makerPermit.permitted.length > 1) {
            // TODO fee recipient
            makerTransferDetails[1] = ISignatureTransfer.SignatureTransferDetails({
                to: 0x2222222222222222222222222222222222222222,
                requestedAmount: makerPermit.permitted[1].amount
            });
            // adjust the maker->recipient payout by the fee amount
            order.makerAmount -= makerPermit.permitted[1].amount;
        }
        makerTransferDetails[0] =
            ISignatureTransfer.SignatureTransferDetails({to: recipient, requestedAmount: order.makerAmount});
        PERMIT2.permitWitnessTransferFrom(
            makerPermit, makerTransferDetails, order.maker, witness, OTC_ORDER_WITNESS, makerSig
        );

        // Taker pays Maker (optional fee)
        ISignatureTransfer.SignatureTransferDetails[] memory takerTransferDetails =
            new ISignatureTransfer.SignatureTransferDetails[](takerPermit.permitted.length);
        takerTransferDetails[0] =
            ISignatureTransfer.SignatureTransferDetails({to: order.maker, requestedAmount: order.takerAmount});
        if (takerPermit.permitted.length > 1) {
            // TODO fee recipient
            takerTransferDetails[1] = ISignatureTransfer.SignatureTransferDetails({
                to: 0x2222222222222222222222222222222222222222,
                requestedAmount: takerPermit.permitted[1].amount
            });
            // No adjustment in payout of taker->maker, maker always receives full amount
        }
        PERMIT2.permitWitnessTransferFrom(
            takerPermit,
            takerTransferDetails,
            order.taker,
            _hashTakerMetatxnOtcOrder(witness, recipient), // witness is completely recomputed
            TAKER_METATXN_OTC_ORDER_WITNESS,
            takerSig
        );

        // TODO actually calculate the orderHash
        emit OtcOrderFilled(
            witness, order.maker, order.taker, order.makerToken, order.takerToken, order.makerAmount, order.takerAmount
        );
    }

    /// @dev Settle an OtcOrder between maker and Settler retaining funds in this contract.
    /// One Permit2 signature is consumed, with the maker Permit2 containing a witness of the OtcOrder.
    // In this variant, Maker pays Settler and Settler pays Maker
    function fillOtcOrderSelfFunded(
        OtcOrder memory order,
        ISignatureTransfer.PermitTransferFrom memory makerPermit,
        bytes memory makerSig,
        uint128 takerTokenFillAmount
    ) internal returns (uint128 takerTokenFilledAmount, uint128 makerTokenFilledAmount) {
        // TODO validate tx.origin and txOrigin
        // TODO adjust amounts based on takerTokenFillAmount

        // Maker pays Settler
        ISignatureTransfer.SignatureTransferDetails memory makerToRecipientTransferDetails =
            ISignatureTransfer.SignatureTransferDetails({to: address(this), requestedAmount: order.makerAmount});
        bytes32 witness = _hashOtcOrder(order);
        PERMIT2.permitWitnessTransferFrom(
            makerPermit, makerToRecipientTransferDetails, order.maker, witness, OTC_ORDER_WITNESS, makerSig
        );

        // Settler pays Maker
        ERC20(order.takerToken).safeTransfer(order.maker, order.takerAmount);
        // TODO actually calculate the orderHash
        emit OtcOrderFilled(
            witness,
            order.maker,
            // TODO fixme
            tx.origin,
            order.makerToken,
            order.takerToken,
            order.makerAmount,
            order.takerAmount
        );
    }
}

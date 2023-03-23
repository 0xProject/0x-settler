// SPDX-License-Identifier: MIT
pragma solidity ^0.8.17;

import {Permit2} from "permit2/src/Permit2.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";

/// @dev An OtcOrder is a simplified and minimized order type. It can only be filled once and
/// has additional requirements for txOrigin
abstract contract OtcOrderSettlement {
    struct OtcOrder {
        address makerToken;
        address takerToken;
        uint128 makerAmount;
        uint128 takerAmount;
        address maker;
        address taker;
        address txOrigin;
    }

    string internal constant OTC_ORDER_WITNESS_TYPE_STRING =
        "OtcOrder order)OtcOrder(address makerToken,address takerToken,uint128 makerAmount,uint128 takerAmount,address maker,address taker,address txOrigin)TokenPermissions(address token,uint256 amount)";

    Permit2 private immutable PERMIT2;

    constructor(address permit2) {
        PERMIT2 = Permit2(permit2);
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
        uint128 takerTokenFillAmount
    ) internal returns (uint128 takerTokenFilledAmount, uint128 makerTokenFilledAmount) {
        // TODO validate order.taker and taker
        // TODO validate tx.origin and txOrigin
        // TODO adjust amounts based on takerTokenFillAmount

        // Maker pays recipient
        ISignatureTransfer.SignatureTransferDetails memory makerToRecipientTransferDetails =
            ISignatureTransfer.SignatureTransferDetails({to: taker, requestedAmount: order.makerAmount});
        bytes32 witness = keccak256(abi.encode(order));
        PERMIT2.permitWitnessTransferFrom(
            makerPermit, makerToRecipientTransferDetails, order.maker, witness, OTC_ORDER_WITNESS_TYPE_STRING, makerSig
        );

        // Taker pays Maker
        ISignatureTransfer.SignatureTransferDetails memory takerToMakerTransferDetails =
            ISignatureTransfer.SignatureTransferDetails({to: order.maker, requestedAmount: order.takerAmount});
        PERMIT2.permitTransferFrom(takerPermit, takerToMakerTransferDetails, taker, takerSig);
    }
}

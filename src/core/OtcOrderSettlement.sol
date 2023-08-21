// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {ERC20} from "solmate/src/tokens/ERC20.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {Permit2Payment} from "./Permit2Payment.sol";

import {SafeTransferLib} from "../utils/SafeTransferLib.sol";

/// @dev An OtcOrder is a simplified and minimized order type. It can only be filled once.
abstract contract OtcOrderSettlement is Permit2Payment {
    using SafeTransferLib for ERC20;

    struct OtcOrder {
        address makerToken;
        address takerToken;
        uint128 makerAmount;
        uint128 takerAmount;
        address maker;
        address taker;
    }

    /// @dev Emitted whenever an `OtcOrder` is filled.
    /// @param orderHash The canonical hash of the order.
    /// @param maker The maker of the order.
    /// @param taker The taker of the order.
    /// @param makerTokenFilledAmount How much maker token was filled.
    /// @param takerTokenFilledAmount How much taker token was filled.
    event OtcOrderFilled(
        bytes32 indexed orderHash,
        address maker,
        address taker,
        address makerToken,
        address takerToken,
        uint128 makerTokenFilledAmount,
        uint128 takerTokenFilledAmount
    );

    string internal constant OTC_ORDER_TYPE =
        "OtcOrder(address makerToken,address takerToken,uint128 makerAmount,uint128 takerAmount,address maker,address taker)";
    // `string.concat` isn't recognized by solc as compile-time constant, but `abi.encodePacked` is
    string internal constant OTC_ORDER_WITNESS =
        string(abi.encodePacked("OtcOrder order)", OTC_ORDER_TYPE, TOKEN_PERMISSIONS_TYPE));
    bytes32 internal constant OTC_ORDER_TYPEHASH = 0x9acbf077fe8e998747874992c0fbe041db1b131cc843ec3d3f81f2ba42bcfc61;

    string internal constant TAKER_METATXN_OTC_ORDER_TYPE = "TakerMetatxnOtcOrder(OtcOrder order,address recipient)";
    string internal constant TAKER_METATXN_OTC_ORDER_TYPE_RECURSIVE =
        string(abi.encodePacked(TAKER_METATXN_OTC_ORDER_TYPE, OTC_ORDER_TYPE));
    string internal constant TAKER_METATXN_OTC_ORDER_WITNESS = string(
        abi.encodePacked(
            "TakerMetatxnOtcOrder order)", OTC_ORDER_TYPE, TAKER_METATXN_OTC_ORDER_TYPE, TOKEN_PERMISSIONS_TYPE
        )
    );
    bytes32 internal constant TAKER_METATXN_OTC_ORDER_TYPEHASH =
        0x27ef1d4e81c48114a28aa80737fddb02a61db3f05627c3cc08848f08a17d569b;

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

    constructor(address permit2) Permit2Payment(permit2) {
        assert(OTC_ORDER_TYPEHASH == keccak256(bytes(OTC_ORDER_TYPE)));
        assert(TAKER_METATXN_OTC_ORDER_TYPEHASH == keccak256(bytes(TAKER_METATXN_OTC_ORDER_TYPE_RECURSIVE)));
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
        uint128 takerTokenFillAmount,
        address recipient
    ) internal returns (uint128 takerTokenFilledAmount, uint128 makerTokenFilledAmount) {
        // TODO validate order.taker and taker
        // TODO adjust amounts based on takerTokenFillAmount

        // TODO: allow multiple fees
        require(makerPermit.permitted.length <= 2, "Invalid Batch Permit2");
        require(takerPermit.permitted.length <= 2, "Invalid Batch Permit2");

        // Maker pays out recipient (optional fee)
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
        permit2WitnessTransferFrom(makerPermit, makerTransferDetails, order.maker, witness, OTC_ORDER_WITNESS, makerSig);

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
        // We don't need to include a witness here. `order.taker` is `msg.sender`, so
        // `recipient` and the maker's details are already authenticated. We're just
        // using PERMIT2 to move tokens, not to provide authentication.
        permit2TransferFrom(takerPermit, takerTransferDetails, order.taker, takerSig);

        // `orderHash` is the OtcOrder struct hash, inclusive of the maker fee (if any),
        // and exclusive of the taker fee (if any). `makerTokenFilledAmount` is the
        // amount sent to the taker (not the fee recipient), exclusive of any transfer
        // fee taken by the maker token. `takerTokenFilledAmount` is the amount sent to
        // the maker (not the fee recipient), exclusive of any transfer fee taken by the
        // taker token.
        emit OtcOrderFilled(
            witness, order.maker, order.taker, order.makerToken, order.takerToken, order.makerAmount, order.takerAmount
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
        // TODO: allow multiple fees
        require(makerPermit.permitted.length <= 2, "Invalid Batch Permit2");
        require(takerPermit.permitted.length <= 2, "Invalid Batch Permit2");

        // Pay close attention to the order in which these operations are
        // performed. It's very important for security and the implications are not
        // intuitive.

        // Maker pays recipient (optional fee)
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
        permit2WitnessTransferFrom(makerPermit, makerTransferDetails, order.maker, witness, OTC_ORDER_WITNESS, makerSig);

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
        permit2WitnessTransferFrom(
            takerPermit,
            takerTransferDetails,
            order.taker,
            _hashTakerMetatxnOtcOrder(order, recipient), // witness is completely recomputed
            TAKER_METATXN_OTC_ORDER_WITNESS,
            takerSig
        );

        // `orderHash` is the OtcOrder struct hash, inclusive of the maker fee (if any),
        // and exclusive of the taker fee (if any). `makerTokenFilledAmount` is the
        // amount sent to the taker (not the fee recipient), exclusive of any transfer
        // fee taken by the maker token. `takerTokenFilledAmount` is the amount sent to
        // the maker (not the fee recipient), exclusive of any transfer fee taken by the
        // taker token.
        emit OtcOrderFilled(
            witness, order.maker, order.taker, order.makerToken, order.takerToken, order.makerAmount, order.takerAmount
        );
    }

    // TODO: fillOtcOrderSelfFunded needs custody optimization

    /// @dev Settle an OtcOrder between maker and Settler retaining funds in this contract.
    /// @dev pre-condition: order.taker has been authenticated against the requestor
    /// One Permit2 signature is consumed, with the maker Permit2 containing a witness of the OtcOrder.
    // In this variant, Maker pays Settler and Settler pays Maker
    function fillOtcOrderSelfFunded(
        OtcOrder memory order,
        ISignatureTransfer.PermitBatchTransferFrom memory permit,
        bytes memory sig,
        uint128 takerTokenFillAmount
    ) internal returns (uint128 takerTokenFilledAmount, uint128 makerTokenFilledAmount) {
        // TODO adjust amounts based on takerTokenFillAmount

        // TODO: allow multiple fees
        require(permit.permitted.length <= 2, "Invalid Batch Permit2");

        // Maker pays Settler
        bytes32 witness = _hashOtcOrder(order);
        ISignatureTransfer.SignatureTransferDetails[] memory transferDetails =
            new ISignatureTransfer.SignatureTransferDetails[](permit.permitted.length);
        transferDetails[0] =
            ISignatureTransfer.SignatureTransferDetails({to: address(this), requestedAmount: order.makerAmount});
        if (permit.permitted.length > 1) {
            // TODO fee recipient
            transferDetails[1] = ISignatureTransfer.SignatureTransferDetails({
                to: 0x2222222222222222222222222222222222222222,
                requestedAmount: permit.permitted[1].amount
            });
            // adjust the maker->recipient payout by the fee amount
            order.makerAmount -= permit.permitted[1].amount;
        }
        permit2WitnessTransferFrom(permit, transferDetails, order.maker, witness, OTC_ORDER_WITNESS, sig);

        // Settler pays Maker
        ERC20(order.takerToken).safeTransfer(order.maker, order.takerAmount);
        emit OtcOrderFilled(
            witness, order.maker, order.taker, order.makerToken, order.takerToken, order.makerAmount, order.takerAmount
        );
    }
}

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {ERC20} from "solmate/src/tokens/ERC20.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {Permit2PaymentAbstract} from "./Permit2Payment.sol";

import {SafeTransferLib} from "../utils/SafeTransferLib.sol";
import {FullMath} from "../utils/FullMath.sol";

abstract contract OtcOrderSettlement is Permit2PaymentAbstract {
    using SafeTransferLib for ERC20;
    using FullMath for uint256;

    struct Consideration {
        address token;
        uint256 amount;
        address counterparty;
        bool partialFillAllowed;
    }

    /// @dev Emitted whenever an OTC order is filled.
    /// @param orderHash The canonical hash of the order. Formed as an EIP712 struct hash. See below.
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
        uint256 makerTokenFilledAmount,
        uint256 takerTokenFilledAmount
    );

    string internal constant CONSIDERATION_TYPE =
        "Consideration(address token,uint256 amount,address counterparty,bool partialFillAllowed)";
    // `string.concat` isn't recognized by solc as compile-time constant, but `abi.encodePacked` is
    string internal constant CONSIDERATION_WITNESS =
        string(abi.encodePacked("Consideration consideration)", CONSIDERATION_TYPE, TOKEN_PERMISSIONS_TYPE));
    bytes32 internal constant CONSIDERATION_TYPEHASH =
        0x7d806873084f389a66fd0315dead7adaad8ae6e8b6cf9fb0d3db61e5a91c3ffa;

    string internal constant TAKER_METATXN_CONSIDERATION_TYPE =
        "TakerMetatxnConsideration(Consideration consideration,address recipient)";
    string internal constant TAKER_METATXN_CONSIDERATION_TYPE_RECURSIVE =
        string(abi.encodePacked(TAKER_METATXN_CONSIDERATION_TYPE, CONSIDERATION_TYPE));
    string internal constant TAKER_METATXN_CONSIDERATION_WITNESS = string(
        abi.encodePacked(
            "TakerMetatxnConsideration consideration)",
            CONSIDERATION_TYPE,
            TAKER_METATXN_CONSIDERATION_TYPE,
            TOKEN_PERMISSIONS_TYPE
        )
    );
    bytes32 internal constant TAKER_METATXN_CONSIDERATION_TYPEHASH =
        0xce50a9f8675c66e6197d1253c716a193f5fff29f4ca719df1f8e5fa761640b6f;

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

    function _hashTakerMetatxnConsideration(Consideration memory consideration, address recipient)
        internal
        pure
        returns (bytes32 result)
    {
        result = _hashConsideration(consideration);
        assembly ("memory-safe") {
            mstore(0x00, TAKER_METATXN_CONSIDERATION_TYPEHASH)
            mstore(0x20, result)
            let ptr := mload(0x40)
            mstore(0x40, recipient)
            result := keccak256(0x00, 0x60)
            mstore(0x40, ptr)
        }
    }

    function _hashOtcOrder(bytes32 makerConsiderationHash, bytes32 takerConsiderationHash)
        internal
        pure
        returns (bytes32 result)
    {
        assembly ("memory-safe") {
            mstore(0x00, OTC_ORDER_TYPEHASH)
            mstore(0x20, makerConsiderationHash)
            let ptr := mload(0x40)
            mstore(0x40, takerConsiderationHash)
            result := keccak256(0x00, 0x60)
            mstore(0x40, ptr)
        }
    }

    constructor() {
        assert(CONSIDERATION_TYPEHASH == keccak256(bytes(CONSIDERATION_TYPE)));
        assert(TAKER_METATXN_CONSIDERATION_TYPEHASH == keccak256(bytes(TAKER_METATXN_CONSIDERATION_TYPE_RECURSIVE)));
        assert(OTC_ORDER_TYPEHASH == keccak256(bytes(OTC_ORDER_TYPE_RECURSIVE)));
    }

    /// @dev Settle an OtcOrder between maker and taker transfering funds directly between
    /// the counterparties. Two Permit2 signatures are consumed, with the maker Permit2 containing
    /// a witness of the OtcOrder.
    /// This variant also includes a fee where the taker or maker pays the fee recipient
    function fillOtcOrder(
        ISignatureTransfer.PermitTransferFrom memory makerPermit,
        address maker,
        bytes memory makerSig,
        ISignatureTransfer.PermitTransferFrom memory takerPermit,
        bytes memory takerSig,
        address recipient
    ) internal {
        (ISignatureTransfer.SignatureTransferDetails memory makerTransferDetails, address buyToken, uint256 buyAmount) =
            _permitToTransferDetails(makerPermit, recipient);

        ISignatureTransfer.SignatureTransferDetails memory takerTransferDetails;
        Consideration memory consideration;
        (takerTransferDetails, consideration.token, consideration.amount) = _permitToTransferDetails(takerPermit, maker);
        consideration.counterparty = msg.sender;

        bytes32 witness = _hashConsideration(consideration);
        // There is no taker witness (see below)

        // Maker pays recipient (optional fee)
        _permit2TransferFrom(makerPermit, makerTransferDetails, maker, witness, CONSIDERATION_WITNESS, makerSig);
        // Taker pays Maker (optional fee)
        // We don't need to include a witness here. Taker is `msg.sender`, so
        // `recipient` and the maker's details are already authenticated. We're just
        // using PERMIT2 to move tokens, not to provide authentication.
        _permit2TransferFrom(takerPermit, takerTransferDetails, msg.sender, takerSig);

        emit OtcOrderFilled(
            _hashOtcOrder(
                witness,
                _hashConsideration(
                    Consideration({token: buyToken, amount: buyAmount, counterparty: maker, partialFillAllowed: false})
                )
            ),
            maker,
            msg.sender,
            buyToken,
            consideration.token,
            buyAmount,
            consideration.amount
        );
    }

    /// @dev Settle an OtcOrder between maker and taker transfering funds directly between
    /// the counterparties. Both Maker and Taker have signed the same order, and submission
    /// is via a third party
    function fillOtcOrderMetaTxn(
        ISignatureTransfer.PermitTransferFrom memory makerPermit,
        address maker,
        bytes memory makerSig,
        ISignatureTransfer.PermitTransferFrom memory takerPermit,
        address taker,
        bytes memory takerSig,
        address recipient
    ) internal {
        ISignatureTransfer.SignatureTransferDetails memory makerTransferDetails;
        Consideration memory takerConsideration;
        (makerTransferDetails, takerConsideration.token, takerConsideration.amount) =
            _permitToTransferDetails(makerPermit, recipient);
        takerConsideration.counterparty = maker;

        ISignatureTransfer.SignatureTransferDetails memory takerTransferDetails;
        Consideration memory makerConsideration;
        (takerTransferDetails, makerConsideration.token, makerConsideration.amount) =
            _permitToTransferDetails(takerPermit, maker);
        makerConsideration.counterparty = taker;

        bytes32 makerWitness = _hashConsideration(makerConsideration);
        bytes32 takerWitness = _hashTakerMetatxnConsideration(takerConsideration, recipient);

        _permit2TransferFrom(makerPermit, makerTransferDetails, maker, makerWitness, CONSIDERATION_WITNESS, makerSig);
        _permit2TransferFrom(
            takerPermit, takerTransferDetails, taker, takerWitness, TAKER_METATXN_CONSIDERATION_WITNESS, takerSig
        );

        emit OtcOrderFilled(
            _hashOtcOrder(makerWitness, takerWitness),
            maker,
            taker,
            takerConsideration.token,
            makerConsideration.token,
            takerConsideration.amount,
            makerConsideration.amount
        );
    }

    // TODO: fillOtcOrderSelfFunded needs custody optimization

    /// @dev Settle an OtcOrder between maker and Settler retaining funds in this contract.
    /// @dev pre-condition: msgSender has been authenticated against the requestor
    /// One Permit2 signature is consumed, with the maker Permit2 containing a witness of the OtcOrder.
    // In this variant, Maker pays Settler and Settler pays Maker
    function fillOtcOrderSelfFunded(
        ISignatureTransfer.PermitTransferFrom memory permit,
        address maker,
        bytes memory sig,
        ERC20 takerToken,
        uint256 maxTakerAmount,
        address msgSender
    ) internal {
        ISignatureTransfer.SignatureTransferDetails memory transferDetails;
        Consideration memory takerConsideration;
        takerConsideration.partialFillAllowed = true;
        (transferDetails, takerConsideration.token, takerConsideration.amount) =
            _permitToTransferDetails(permit, address(this));
        takerConsideration.counterparty = maker;

        Consideration memory makerConsideration = Consideration({
            token: address(takerToken),
            amount: maxTakerAmount,
            counterparty: msgSender,
            partialFillAllowed: true
        });
        bytes32 witness = _hashConsideration(makerConsideration);

        uint256 takerAmount = takerToken.balanceOf(address(this));
        if (takerAmount >= maxTakerAmount) {
            takerAmount = maxTakerAmount;
        }
        transferDetails.requestedAmount = transferDetails.requestedAmount.unsafeMulDiv(takerAmount, maxTakerAmount);

        _permit2TransferFrom(permit, transferDetails, maker, witness, CONSIDERATION_WITNESS, sig);
        takerToken.safeTransfer(maker, takerAmount);

        emit OtcOrderFilled(
            _hashOtcOrder(witness, _hashConsideration(takerConsideration)),
            maker,
            msgSender,
            takerConsideration.token,
            address(takerToken),
            transferDetails.requestedAmount,
            takerAmount
        );
    }
}

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

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
            mstore(0x10, makerFilledAmount)
            mstore(0x00, orderHash)
            log0(0x00, 0x30)
            mstore(0x40, ptr)
        }
    }

    constructor() {
        assert(CONSIDERATION_TYPEHASH == keccak256(bytes(CONSIDERATION_TYPE)));
        assert(OTC_ORDER_TYPEHASH == keccak256(bytes(OTC_ORDER_TYPE_RECURSIVE)));
    }

    /// @dev Settle an OtcOrder between maker and taker transfering funds directly between
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
        (ISignatureTransfer.SignatureTransferDetails memory makerTransferDetails, address buyToken, uint256 buyAmount) =
            _permitToTransferDetails(makerPermit, recipient);

        address taker = _msgSender();
        ISignatureTransfer.SignatureTransferDetails memory takerTransferDetails;
        Consideration memory consideration;
        (takerTransferDetails, consideration.token, consideration.amount) = _permitToTransferDetails(takerPermit, maker);
        consideration.counterparty = taker;

        bytes32 witness = _hashConsideration(consideration);
        // There is no taker witness (see below)

        // Taker pays Maker
        // We don't need to include a witness here. Taker is `_msgSender()`, so
        // `recipient` and the maker's details are already authenticated. We're just
        // using Permit2 or AllowanceHolder to move tokens, not to provide authentication.
        _transferFrom(takerPermit, takerTransferDetails, taker, takerSig);
        // Maker pays recipient
        _setWitness(witness);
        _transferFrom(makerPermit, makerTransferDetails, maker, CONSIDERATION_WITNESS, makerSig, false);

        _logOtcOrder(
            witness,
            _hashConsideration(
                Consideration({token: buyToken, amount: buyAmount, counterparty: maker, partialFillAllowed: false})
            ),
            uint128(buyAmount)
        );
    }

    /// @dev Settle an OtcOrder between maker and taker transfering funds directly between
    /// the counterparties. Both Maker and Taker have signed the same order, and submission
    /// is via a third party
    /// @dev `takerWitness` is not calculated nor verified here as caller is trusted
    function fillOtcOrderMetaTxn(
        address recipient,
        ISignatureTransfer.PermitTransferFrom memory makerPermit,
        address maker,
        bytes memory makerSig,
        ISignatureTransfer.PermitTransferFrom memory takerPermit,
        address taker,
        bytes memory takerSig
    ) internal {
        ISignatureTransfer.SignatureTransferDetails memory makerTransferDetails;
        Consideration memory takerConsideration;
        uint256 buyAmount;
        (makerTransferDetails, takerConsideration.token, buyAmount) = _permitToTransferDetails(makerPermit, recipient);
        takerConsideration.amount = buyAmount;
        takerConsideration.counterparty = maker;

        ISignatureTransfer.SignatureTransferDetails memory takerTransferDetails;
        Consideration memory makerConsideration;
        (takerTransferDetails, makerConsideration.token, makerConsideration.amount) =
            _permitToTransferDetails(takerPermit, maker);
        makerConsideration.counterparty = taker;

        bytes32 makerWitness = _hashConsideration(makerConsideration);
        // Note: takerWitness is not calculated here, but in the caller code

        _transferFrom(takerPermit, takerTransferDetails, taker, ACTIONS_AND_SLIPPAGE_WITNESS, takerSig);
        _setWitness(makerWitness);
        _transferFrom(makerPermit, makerTransferDetails, maker, CONSIDERATION_WITNESS, makerSig, false);

        _logOtcOrder(makerWitness, _hashConsideration(takerConsideration), uint128(buyAmount));
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
        ISignatureTransfer.SignatureTransferDetails memory transferDetails;
        Consideration memory takerConsideration;
        takerConsideration.partialFillAllowed = true;
        uint256 buyAmount;
        (transferDetails, takerConsideration.token, buyAmount) = _permitToTransferDetails(permit, recipient);
        takerConsideration.amount = buyAmount;
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

        takerToken.safeTransfer(maker, takerAmount);
        _setWitness(witness);
        _transferFrom(permit, transferDetails, maker, CONSIDERATION_WITNESS, makerSig, false);

        _logOtcOrder(witness, _hashConsideration(takerConsideration), uint128(buyAmount));
    }
}

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {SettlerAbstract} from "../SettlerAbstract.sol";

import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {FullMath} from "../vendor/FullMath.sol";
import {Ternary} from "../utils/Ternary.sol";

abstract contract RfqOrderSettlement is SettlerAbstract {
    using Ternary for bool;
    using SafeTransferLib for IERC20;
    using FullMath for uint256;

    struct Consideration {
        IERC20 token;
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

    string internal constant RFQ_ORDER_TYPE =
        "RfqOrder(Consideration makerConsideration,Consideration takerConsideration)";
    string internal constant RFQ_ORDER_TYPE_RECURSIVE = string(abi.encodePacked(RFQ_ORDER_TYPE, CONSIDERATION_TYPE));
    bytes32 internal constant RFQ_ORDER_TYPEHASH = 0x49fa719b76f0f6b7e76be94b56c26671a548e1c712d5b13dc2874f70a7598276;

    function _hashConsideration(Consideration memory consideration) internal pure returns (bytes32 result) {
        assembly ("memory-safe") {
            let ptr := sub(consideration, 0x20)
            let oldValue := mload(ptr)
            mstore(ptr, CONSIDERATION_TYPEHASH)
            result := keccak256(ptr, 0xa0)
            mstore(ptr, oldValue)
        }
    }

    function _logRfqOrder(bytes32 makerConsiderationHash, bytes32 takerConsiderationHash, uint128 makerFilledAmount)
        private
    {
        assembly ("memory-safe") {
            mstore(0x00, RFQ_ORDER_TYPEHASH)
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
        assert(RFQ_ORDER_TYPEHASH == keccak256(bytes(RFQ_ORDER_TYPE_RECURSIVE)));
    }

    /// @dev Settle an RfqOrder between maker and taker transferring funds directly between the counterparties. Either
    ///      two Permit2 signatures are consumed, with the maker Permit2 containing a witness of the RfqOrder, or
    ///      AllowanceHolder is supported for the taker payment. The Maker has signed the same order as the
    ///      Taker. Submission may be directly by the taker or via a third party with the Taker signing a witness.
    /// @dev if used, the taker's witness is not calculated nor verified here as calling function is trusted
    function fillRfqOrderVIP(
        address recipient,
        ISignatureTransfer.PermitTransferFrom memory makerPermit,
        address maker,
        bytes memory makerSig,
        ISignatureTransfer.PermitTransferFrom memory takerPermit,
        bytes memory takerSig
    ) internal {
        if (!_hasMetaTxn()) {
            assert(makerPermit.permitted.amount <= type(uint256).max - BASIS);
        }
        (ISignatureTransfer.SignatureTransferDetails memory makerTransferDetails, uint256 makerAmount) =
            _permitToTransferDetails(makerPermit, recipient);
        // In theory, the taker permit could invoke the balance-proportional sell amount logic. However,
        // because we hash the sell amount computed here into the maker's consideration (witness) only a
        // balance-proportional sell amount that corresponds exactly to the signed order would avoid a
        // revert. In other words, no unexpected behavior is possible. It's pointless to prohibit the
        // use of that logic.
        (ISignatureTransfer.SignatureTransferDetails memory takerTransferDetails, uint256 takerAmount) =
            _permitToTransferDetails(takerPermit, maker);

        bytes32 witness = _hashConsideration(
            Consideration({
                token: IERC20(takerPermit.permitted.token),
                amount: takerAmount,
                counterparty: _msgSender(),
                partialFillAllowed: false
            })
        );
        _transferFrom(takerPermit, takerTransferDetails, takerSig);
        _transferFromIKnowWhatImDoing(
            makerPermit, makerTransferDetails, maker, witness, CONSIDERATION_WITNESS, makerSig, false
        );

        _logRfqOrder(
            witness,
            _hashConsideration(
                Consideration({
                    token: IERC20(makerPermit.permitted.token),
                    amount: makerAmount,
                    counterparty: maker,
                    partialFillAllowed: false
                })
            ),
            uint128(makerAmount)
        );
    }

    /// @dev Settle an RfqOrder between maker and Settler retaining funds in this contract.
    /// @dev pre-condition: msgSender has been authenticated against the requestor
    /// One Permit2 signature is consumed, with the maker Permit2 containing a witness of the RfqOrder.
    // In this variant, Maker pays recipient and Settler pays Maker
    function fillRfqOrderSelfFunded(
        address recipient,
        ISignatureTransfer.PermitTransferFrom memory permit,
        address maker,
        bytes memory makerSig,
        IERC20 takerToken,
        uint256 maxTakerAmount
    ) internal {
        if (!_hasMetaTxn()) {
            assert(permit.permitted.amount <= type(uint256).max - BASIS);
        }
        // Compute witnesses. These are based on the quoted maximum amounts. We will modify them
        // later to adjust for the actual settled amount, which may be modified by encountered
        // slippage.
        (ISignatureTransfer.SignatureTransferDetails memory transferDetails, uint256 makerAmount) =
            _permitToTransferDetails(permit, recipient);

        bytes32 takerWitness = _hashConsideration(
            Consideration({
                token: IERC20(permit.permitted.token),
                amount: makerAmount,
                counterparty: maker,
                partialFillAllowed: true
            })
        );
        bytes32 makerWitness = _hashConsideration(
            Consideration({
                token: takerToken,
                amount: maxTakerAmount,
                counterparty: _msgSender(),
                partialFillAllowed: true
            })
        );

        // Now we adjust the transfer amounts to compensate for encountered slippage. Rounding is
        // performed in the maker's favor.
        uint256 takerAmount = takerToken.fastBalanceOf(address(this));
        takerAmount = (takerAmount > maxTakerAmount).ternary(maxTakerAmount, takerAmount);
        transferDetails.requestedAmount = makerAmount = makerAmount.unsafeMulDiv(takerAmount, maxTakerAmount);

        // Now that we have all the relevant information, make the transfers and log the order.
        takerToken.safeTransfer(maker, takerAmount);
        _transferFromIKnowWhatImDoing(
            permit, transferDetails, maker, makerWitness, CONSIDERATION_WITNESS, makerSig, false
        );

        _logRfqOrder(makerWitness, takerWitness, uint128(makerAmount));
    }
}

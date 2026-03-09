// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {RfqOrderSettlement} from "src/core/RfqOrderSettlement.sol";
import {Permit2PaymentAbstract} from "src/core/Permit2PaymentAbstract.sol";
import {
    Permit2PaymentMetaTxn,
    Permit2PaymentTakerSubmitted,
    Permit2Payment,
    Permit2PaymentBase
} from "src/core/Permit2Payment.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {IAllowanceHolder} from "src/allowanceholder/IAllowanceHolder.sol";
import {Context, AbstractContext} from "src/Context.sol";
import {AllowanceHolderContext} from "src/allowanceholder/AllowanceHolderContext.sol";

import {uint512} from "src/utils/512Math.sol";

import {Utils} from "../Utils.sol";
import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {Test} from "@forge-std/Test.sol";

abstract contract RfqOrderSettlementDummyBase is RfqOrderSettlement, Permit2Payment {
    function considerationWitnessType() external pure returns (string memory) {
        return CONSIDERATION_WITNESS;
    }

    function actionsAndSlippageWitnessType() external pure returns (string memory) {
        return string(
            abi.encodePacked(
                "SlippageAndActions slippageAndActions)", SLIPPAGE_AND_ACTIONS_TYPE, TOKEN_PERMISSIONS_TYPE
            )
        );
    }

    function _tokenId() internal pure override returns (uint256) {
        revert("unimplemented");
    }

    function _isRestrictedTarget(address target)
        internal
        view
        virtual
        override(Permit2PaymentBase, Permit2PaymentAbstract)
        returns (bool)
    {
        return super._isRestrictedTarget(target);
    }
}

contract RfqOrderSettlementDummy is Permit2PaymentTakerSubmitted, RfqOrderSettlementDummyBase {
    function fillRfqOrderDirectCounterparties(
        address recipient,
        ISignatureTransfer.PermitTransferFrom memory makerPermit,
        address maker,
        bytes memory makerSig,
        ISignatureTransfer.PermitTransferFrom memory takerPermit,
        bytes memory takerSig
    ) external takerSubmitted {
        super.fillRfqOrderVIP(recipient, makerPermit, maker, makerSig, takerPermit, takerSig);
    }

    function fillRfqOrderSelf(
        address recipient,
        ISignatureTransfer.PermitTransferFrom memory permit,
        address maker,
        bytes memory makerSig,
        address takerToken,
        uint256 maxTakerAmount
    ) external takerSubmitted {
        super.fillRfqOrderSelfFunded(recipient, permit, maker, makerSig, IERC20(takerToken), maxTakerAmount);
    }

    function _hasMetaTxn() internal pure override returns (bool) {
        return false;
    }

    function _msgSender()
        internal
        view
        override(Permit2PaymentTakerSubmitted, Permit2PaymentBase, AbstractContext)
        returns (address)
    {
        return super._msgSender();
    }

    function _msgData()
        internal
        view
        override(AbstractContext, Context, Permit2PaymentTakerSubmitted)
        returns (bytes calldata)
    {
        return super._msgData();
    }

    function _isForwarded()
        internal
        view
        override(AbstractContext, Context, Permit2PaymentTakerSubmitted)
        returns (bool)
    {
        return super._isForwarded();
    }

    function _isRestrictedTarget(address target)
        internal
        view
        override(Permit2PaymentTakerSubmitted, RfqOrderSettlementDummyBase)
        returns (bool)
    {
        return super._isRestrictedTarget(target);
    }

    function _dispatch(uint256, uint256, bytes calldata) internal pure override returns (bool) {
        revert("unimplemented");
    }

    function _div512to256(uint512, uint512) internal view override returns (uint256) {
        revert("unimplemented");
    }
}

contract RfqOrderSettlementMetaTxnDummy is Permit2PaymentMetaTxn, RfqOrderSettlementDummyBase {
    function fillRfqOrderMeta(
        address recipient,
        ISignatureTransfer.PermitTransferFrom memory makerPermit,
        address maker,
        bytes memory makerSig,
        ISignatureTransfer.PermitTransferFrom memory takerPermit,
        address taker,
        bytes memory takerSig,
        bytes32 takerWitness
    ) external metaTx(taker, takerWitness) {
        super.fillRfqOrderVIP(recipient, makerPermit, maker, makerSig, takerPermit, takerSig);
    }

    function _hasMetaTxn() internal pure override returns (bool) {
        return true;
    }

    function _msgSender()
        internal
        view
        override(Permit2PaymentMetaTxn, Permit2PaymentBase, AbstractContext)
        returns (address)
    {
        return super._msgSender();
    }

    function _isRestrictedTarget(address target)
        internal
        view
        override(Permit2PaymentBase, RfqOrderSettlementDummyBase)
        returns (bool)
    {
        return super._isRestrictedTarget(target);
    }

    function _dispatch(uint256, uint256, bytes calldata) internal pure override returns (bool) {
        revert("unimplemented");
    }

    function _div512to256(uint512, uint512) internal view override returns (uint256) {
        revert("unimplemented");
    }
}

contract RfqUnitTest is Utils, Test {
    RfqOrderSettlementDummy rfq;
    RfqOrderSettlementMetaTxnDummy rfqMeta;
    address PERMIT2 = _etchNamedRejectionDummy("PERMIT2", 0x000000000022D473030F116dDEE9F6B43aC78BA3);
    address ALLOWANCE_HOLDER = _etchNamedRejectionDummy("ALLOWANCE_HOLDER", 0x0000000000001fF3684f28c67538d4D072C22734);

    address TOKEN0 = _createNamedRejectionDummy("TOKEN0");
    address TOKEN1 = _createNamedRejectionDummy("TOKEN1");
    address RECIPIENT = _createNamedRejectionDummy("RECIPIENT");
    address MAKER = _createNamedRejectionDummy("MAKER");

    function _emitRfqOrder(bytes32 orderHash, uint128 fillAmount) internal {
        assembly ("memory-safe") {
            mstore(0x00, orderHash)
            mstore(0x20, shl(0x80, fillAmount))
            log0(0x00, 0x30)
        }
    }

    function setUp() public {
        rfq = new RfqOrderSettlementDummy();
        rfqMeta = new RfqOrderSettlementMetaTxnDummy();
    }

    function testRfqDirectCounterparties() public {
        // 🎉
        uint256 amount = 9999;
        ISignatureTransfer.PermitTransferFrom memory makerPermit = ISignatureTransfer.PermitTransferFrom({
            permitted: ISignatureTransfer.TokenPermissions({token: TOKEN1, amount: amount}),
            nonce: 0,
            deadline: 0
        });
        ISignatureTransfer.PermitTransferFrom memory takerPermit = ISignatureTransfer.PermitTransferFrom({
            permitted: ISignatureTransfer.TokenPermissions({token: TOKEN0, amount: amount}),
            nonce: 0,
            deadline: 0
        });

        ISignatureTransfer.SignatureTransferDetails memory transferDetails =
            ISignatureTransfer.SignatureTransferDetails({to: RECIPIENT, requestedAmount: amount});
        bytes32 witness = keccak256(
            abi.encode(
                keccak256("Consideration(address token,uint256 amount,address counterparty,bool partialFillAllowed)"),
                TOKEN0,
                amount,
                address(this),
                false
            )
        );

        bytes memory witnessTypeString = bytes(rfq.considerationWitnessType());
        // the calldata is somewhat tortured here because Settler produces a non-strict ABI encoding
        // when calling Permit2
        _mockExpectCall(
            PERMIT2,
            bytes.concat(
                abi.encodeWithSelector(
                    bytes4(0x137c29fe),
                    makerPermit,
                    transferDetails,
                    MAKER,
                    witness,
                    uint256(0x140),
                    uint256(0x160 + witnessTypeString.length)
                ),
                abi.encodePacked(witnessTypeString.length, witnessTypeString, uint256(2), hex"dead")
            ),
            new bytes(0)
        );
        _mockExpectCall(
            PERMIT2,
            bytes.concat(
                abi.encodeWithSelector(
                    bytes4(0x30f28b7a),
                    takerPermit,
                    ISignatureTransfer.SignatureTransferDetails({to: MAKER, requestedAmount: amount}),
                    address(this), /* taker + payer */
                    uint256(0x100)
                ),
                abi.encodePacked(uint256(2), hex"beef")
            ),
            new bytes(0)
        );

        //// https://github.com/foundry-rs/foundry/issues/7457
        // vm.expectEmit(address(rfq));
        // _emitRfqOrder(
        //     keccak256(
        //         abi.encode(
        //             keccak256(
        //                 "RfqOrder(Consideration makerConsideration,Consideration takerConsideration)Consideration(address token,uint256 amount,address counterparty,bool partialFillAllowed)"
        //             ),
        //             witness,
        //             keccak256(
        //                 abi.encode(
        //                     keccak256(
        //                         "Consideration(address token,uint256 amount,address counterparty,bool partialFillAllowed)"
        //                     ),
        //                     TOKEN1,
        //                     amount,
        //                     MAKER,
        //                     false
        //                 )
        //             )
        //         )
        //     ),
        //     uint128(amount)
        // );

        rfq.fillRfqOrderDirectCounterparties(RECIPIENT, makerPermit, MAKER, hex"dead", takerPermit, hex"beef");
    }

    function testRfqDirectCounterpartiesViaAllowanceHolder() public {
        uint256 amount = 9999;
        ISignatureTransfer.PermitTransferFrom memory makerPermit = ISignatureTransfer.PermitTransferFrom({
            permitted: ISignatureTransfer.TokenPermissions({token: TOKEN1, amount: amount}),
            nonce: 0,
            deadline: block.timestamp
        });
        ISignatureTransfer.PermitTransferFrom memory takerPermit = ISignatureTransfer.PermitTransferFrom({
            permitted: ISignatureTransfer.TokenPermissions({token: TOKEN0, amount: amount}),
            nonce: 0,
            deadline: block.timestamp
        });

        ISignatureTransfer.SignatureTransferDetails memory transferDetails =
            ISignatureTransfer.SignatureTransferDetails({to: RECIPIENT, requestedAmount: amount});
        bytes32 witness = keccak256(
            abi.encode(
                keccak256("Consideration(address token,uint256 amount,address counterparty,bool partialFillAllowed)"),
                TOKEN0,
                amount,
                address(this),
                false
            )
        );
        bytes memory witnessTypeString = bytes(rfq.considerationWitnessType());
        // the calldata is somewhat tortured here because Settler produces a non-strict ABI encoding
        // when calling Permit2
        _mockExpectCall(
            PERMIT2,
            bytes.concat(
                abi.encodeWithSelector(
                    bytes4(0x137c29fe),
                    makerPermit,
                    transferDetails,
                    MAKER,
                    witness,
                    uint256(0x140),
                    uint256(0x160 + witnessTypeString.length)
                ),
                abi.encodePacked(witnessTypeString.length, witnessTypeString, uint256(2), hex"dead")
            ),
            new bytes(0)
        );

        _mockExpectCall(
            ALLOWANCE_HOLDER,
            abi.encodeCall(IAllowanceHolder.transferFrom, (TOKEN0, address(this), MAKER, amount)),
            abi.encode(true)
        );

        //// https://github.com/foundry-rs/foundry/issues/7457
        // vm.expectEmit(address(rfq));
        // _emitRfqOrder(
        //     keccak256(
        //         abi.encode(
        //             keccak256(
        //                 "RfqOrder(Consideration makerConsideration,Consideration takerConsideration)Consideration(address token,uint256 amount,address counterparty,bool partialFillAllowed)"
        //             ),
        //             witness,
        //             keccak256(
        //                 abi.encode(
        //                     keccak256(
        //                         "Consideration(address token,uint256 amount,address counterparty,bool partialFillAllowed)"
        //                     ),
        //                     TOKEN1,
        //                     amount,
        //                     MAKER,
        //                     false
        //                 )
        //             )
        //         )
        //     ),
        //     uint128(amount)
        // );

        vm.prank(ALLOWANCE_HOLDER);
        (bool success,) = address(rfq).call(
            abi.encodePacked(
                abi.encodeCall(
                    rfq.fillRfqOrderDirectCounterparties, (RECIPIENT, makerPermit, MAKER, hex"dead", takerPermit, hex"")
                ),
                address(this)
            ) // Forward on true msg.sender
        );
        require(success);
    }

    function testRfqSelfFunded() public {
        uint256 amount = 9999;
        ISignatureTransfer.PermitTransferFrom memory makerPermit = ISignatureTransfer.PermitTransferFrom({
            permitted: ISignatureTransfer.TokenPermissions({token: TOKEN1, amount: amount}),
            nonce: 0,
            deadline: 0
        });

        ISignatureTransfer.SignatureTransferDetails memory transferDetails =
            ISignatureTransfer.SignatureTransferDetails({to: RECIPIENT, requestedAmount: amount});
        bytes32 witness = keccak256(
            abi.encode(
                keccak256("Consideration(address token,uint256 amount,address counterparty,bool partialFillAllowed)"),
                TOKEN0,
                amount,
                address(this),
                true
            )
        );
        bytes memory witnessTypeString = bytes(rfq.considerationWitnessType());

        // the calldata is somewhat tortured here because Settler produces a non-strict ABI encoding
        // when calling Permit2
        _mockExpectCall(
            PERMIT2,
            bytes.concat(
                abi.encodeWithSelector(
                    bytes4(0x137c29fe),
                    makerPermit,
                    transferDetails,
                    MAKER,
                    witness,
                    uint256(0x140),
                    uint256(0x160 + witnessTypeString.length)
                ),
                abi.encodePacked(witnessTypeString.length, witnessTypeString, uint256(2), hex"dead")
            ),
            new bytes(0)
        );

        _mockExpectCall(
            address(TOKEN0), abi.encodeWithSelector(IERC20.balanceOf.selector, address(rfq)), abi.encode(amount)
        );

        _mockExpectCall(
            address(TOKEN0), abi.encodeWithSelector(IERC20.transfer.selector, MAKER, amount), abi.encode(true)
        );

        //// https://github.com/foundry-rs/foundry/issues/7457
        // vm.expectEmit(address(rfq));
        // _emitRfqOrder(
        //     keccak256(
        //         abi.encode(
        //             keccak256(
        //                 "RfqOrder(Consideration makerConsideration,Consideration takerConsideration)Consideration(address token,uint256 amount,address counterparty,bool partialFillAllowed)"
        //             ),
        //             witness,
        //             keccak256(
        //                 abi.encode(
        //                     keccak256(
        //                         "Consideration(address token,uint256 amount,address counterparty,bool partialFillAllowed)"
        //                     ),
        //                     TOKEN1,
        //                     amount,
        //                     MAKER,
        //                     true
        //                 )
        //             )
        //         )
        //     ),
        //     uint128(amount)
        // );

        rfq.fillRfqOrderSelf(RECIPIENT, makerPermit, MAKER, hex"dead", TOKEN0, amount);
    }

    function testRfqMetaTxn() public {
        address taker = address(0xc0de60d);

        uint256 amount = 9999;
        ISignatureTransfer.PermitTransferFrom memory makerPermit = ISignatureTransfer.PermitTransferFrom({
            permitted: ISignatureTransfer.TokenPermissions({token: TOKEN1, amount: amount}),
            nonce: 0,
            deadline: 0
        });
        ISignatureTransfer.PermitTransferFrom memory takerPermit = ISignatureTransfer.PermitTransferFrom({
            permitted: ISignatureTransfer.TokenPermissions({token: TOKEN0, amount: amount}),
            nonce: 0,
            deadline: 0
        });

        ISignatureTransfer.SignatureTransferDetails memory transferDetails =
            ISignatureTransfer.SignatureTransferDetails({to: RECIPIENT, requestedAmount: amount});
        bytes32 witness = keccak256(
            abi.encode(
                keccak256("Consideration(address token,uint256 amount,address counterparty,bool partialFillAllowed)"),
                TOKEN0,
                amount,
                taker,
                false
            )
        );

        bytes memory actionsAndSlippageWitnessType = bytes(rfqMeta.actionsAndSlippageWitnessType());
        bytes memory considerationWitnessType = bytes(rfqMeta.considerationWitnessType());
        // the calldata is somewhat tortured here because Settler produces a non-strict ABI encoding
        // when calling Permit2

        // Taker payment via Permit2
        _mockExpectCall(
            PERMIT2,
            bytes.concat(
                abi.encodeWithSelector(
                    bytes4(0x137c29fe),
                    takerPermit,
                    ISignatureTransfer.SignatureTransferDetails({to: MAKER, requestedAmount: amount}),
                    taker,
                    bytes32(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), /* witness */
                    uint256(0x140),
                    uint256(0x160 + actionsAndSlippageWitnessType.length)
                ),
                abi.encodePacked(
                    actionsAndSlippageWitnessType.length, actionsAndSlippageWitnessType, uint256(2), hex"beef"
                )
            ),
            new bytes(0)
        );

        // Maker payment via Permit2
        _mockExpectCall(
            PERMIT2,
            bytes.concat(
                abi.encodeWithSelector(
                    bytes4(0x137c29fe),
                    makerPermit,
                    transferDetails,
                    MAKER,
                    witness,
                    uint256(0x140),
                    uint256(0x160 + considerationWitnessType.length)
                ),
                abi.encodePacked(considerationWitnessType.length, considerationWitnessType, uint256(2), hex"dead")
            ),
            new bytes(0)
        );

        //// https://github.com/foundry-rs/foundry/issues/7457
        // vm.expectEmit(address(rfqMeta));
        // _emitRfqOrder(
        //     keccak256(
        //         abi.encode(
        //             keccak256(
        //                 "RfqOrder(Consideration makerConsideration,Consideration takerConsideration)Consideration(address token,uint256 amount,address counterparty,bool partialFillAllowed)"
        //             ),
        //             witness,
        //             keccak256(
        //                 abi.encode(
        //                     keccak256(
        //                         "Consideration(address token,uint256 amount,address counterparty,bool partialFillAllowed)"
        //                     ),
        //                     TOKEN1,
        //                     amount,
        //                     MAKER,
        //                     false
        //                 )
        //             )
        //         )
        //     ),
        //     uint128(amount)
        // );

        rfqMeta.fillRfqOrderMeta(
            RECIPIENT,
            makerPermit,
            MAKER,
            hex"dead",
            takerPermit,
            taker,
            hex"beef",
            bytes32(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
        );
    }
}

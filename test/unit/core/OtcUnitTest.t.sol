// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {OtcOrderSettlement} from "../../../src/core/OtcOrderSettlement.sol";
import {Permit2Payment} from "../../../src/core/Permit2Payment.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {IAllowanceHolder} from "../../../src/IAllowanceHolder.sol";

import {Utils} from "../Utils.sol";
import {IERC20} from "../../../src/IERC20.sol";

import {Test} from "forge-std/Test.sol";

contract OtcOrderSettlementDummy is OtcOrderSettlement, Permit2Payment {
    constructor(address permit2, address feeRecipient, address allowanceHolder)
        Permit2Payment(permit2, feeRecipient, allowanceHolder)
    {}

    function considerationWitnessType() external pure returns (string memory) {
        return CONSIDERATION_WITNESS;
    }

    function actionsAndSlippageWitnessType() external pure returns (string memory) {
        return ACTIONS_AND_SLIPPAGE_WITNESS;
    }

    function fillOtcOrderDirectCounterparties(
        address recipient,
        ISignatureTransfer.PermitTransferFrom memory makerPermit,
        address maker,
        bytes memory makerSig,
        ISignatureTransfer.PermitTransferFrom memory takerPermit,
        bytes memory takerSig
    ) external {
        super.fillOtcOrder(recipient, makerPermit, maker, makerSig, takerPermit, takerSig);
    }

    function fillOtcOrderSelf(
        address recipient,
        ISignatureTransfer.PermitTransferFrom memory permit,
        address maker,
        bytes memory makerSig,
        address takerToken,
        uint256 maxTakerAmount,
        address msgSender
    ) external {
        super.fillOtcOrderSelfFunded(recipient, permit, maker, makerSig, IERC20(takerToken), maxTakerAmount, msgSender);
    }

    function fillOtcOrderMeta(
        address recipient,
        ISignatureTransfer.PermitTransferFrom memory makerPermit,
        address maker,
        bytes memory makerSig,
        ISignatureTransfer.PermitTransferFrom memory takerPermit,
        address taker,
        bytes memory takerSig,
        bytes32 takerWitness
    ) external {
        super.fillOtcOrderMetaTxn(recipient, makerPermit, maker, makerSig, takerPermit, taker, takerSig, takerWitness);
    }
}

contract OtcUnitTest is Utils, Test {
    OtcOrderSettlementDummy otc;
    address PERMIT2 = _createNamedRejectionDummy("PERMIT2");
    address FEE_RECIPIENT = _createNamedRejectionDummy("FEE_RECIPIENT");
    address ALLOWANCE_HOLDER = _createNamedRejectionDummy("ALLOWANCE_HOLDER");

    address TOKEN0 = _createNamedRejectionDummy("TOKEN0");
    address TOKEN1 = _createNamedRejectionDummy("TOKEN1");
    address RECIPIENT = _createNamedRejectionDummy("RECIPIENT");
    address MAKER = _createNamedRejectionDummy("MAKER");

    function setUp() public {
        otc = new OtcOrderSettlementDummy(PERMIT2, FEE_RECIPIENT, ALLOWANCE_HOLDER);
    }

    function testOtcDirectCounterparties() public {
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

        _mockExpectCall(
            PERMIT2,
            abi.encodeWithSelector(
                bytes4(0x137c29fe),
                makerPermit,
                ISignatureTransfer.SignatureTransferDetails({to: RECIPIENT, requestedAmount: amount}),
                MAKER,
                bytes32(0x315954c1f9717c9d14604de3c6ceb9fd601b3bd1d0b8ec397e8c2b81668a02e1), /* witness */
                otc.considerationWitnessType(),
                hex"dead"
            ),
            new bytes(0)
        );

        _mockExpectCall(
            PERMIT2,
            abi.encodeWithSelector(
                bytes4(0x30f28b7a),
                takerPermit,
                ISignatureTransfer.SignatureTransferDetails({to: MAKER, requestedAmount: amount}),
                address(this), /* taker + payer */
                hex"beef"
            ),
            new bytes(0)
        );

        // Broken usage of OtcOrderSettlement.OtcOrderFilled in 0.8.21
        //      https://github.com/foundry-rs/foundry/issues/6206
        // vm.expectEmit(address(otc));
        // emit OtcOrderSettlement.OtcOrderFilled(
        //     bytes32(0xbee0e2de3e64ecfe06fe7118215a033ac40a8d6a508d60b81cd9ac6addd6e11e),
        //     MAKER,
        //     address(this),
        //     TOKEN1,
        //     TOKEN0,
        //     amount,
        //     amount
        // );

        otc.fillOtcOrderDirectCounterparties(RECIPIENT, makerPermit, MAKER, hex"dead", takerPermit, hex"beef");
    }

    function testOtcDirectCounterpartiesViaAllowanceHolder() public {
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

        _mockExpectCall(
            PERMIT2,
            abi.encodeWithSelector(
                bytes4(0x137c29fe),
                makerPermit,
                ISignatureTransfer.SignatureTransferDetails({to: RECIPIENT, requestedAmount: amount}),
                MAKER,
                bytes32(0x315954c1f9717c9d14604de3c6ceb9fd601b3bd1d0b8ec397e8c2b81668a02e1), /* witness */
                otc.considerationWitnessType(),
                hex"dead"
            ),
            new bytes(0)
        );

        IAllowanceHolder.TransferDetails[] memory transferDetails = new IAllowanceHolder.TransferDetails[](1);
        transferDetails[0] = IAllowanceHolder.TransferDetails({token: TOKEN0, recipient: MAKER, amount: amount});

        _mockExpectCall(
            ALLOWANCE_HOLDER,
            abi.encodeCall(IAllowanceHolder.holderTransferFrom, (address(this), transferDetails)),
            abi.encode(true)
        );

        // Broken usage of OtcOrderSettlement.OtcOrderFilled in 0.8.21
        //      https://github.com/foundry-rs/foundry/issues/6206
        // vm.expectEmit(address(otc));
        // emit OtcOrderSettlement.OtcOrderFilled(
        //     bytes32(0xbee0e2de3e64ecfe06fe7118215a033ac40a8d6a508d60b81cd9ac6addd6e11e),
        //     MAKER,
        //     address(this),
        //     TOKEN1,
        //     TOKEN0,
        //     amount,
        //     amount
        // );

        vm.prank(ALLOWANCE_HOLDER);
        (bool success,) = address(otc).call(
            abi.encodePacked(
                abi.encodeCall(
                    otc.fillOtcOrderDirectCounterparties, (RECIPIENT, makerPermit, MAKER, hex"dead", takerPermit, hex"")
                ),
                address(this)
            ) // Forward on true msg.sender
        );
        require(success);
    }

    function testOtcSelfFunded() public {
        uint256 amount = 9999;
        ISignatureTransfer.PermitTransferFrom memory makerPermit = ISignatureTransfer.PermitTransferFrom({
            permitted: ISignatureTransfer.TokenPermissions({token: TOKEN1, amount: amount}),
            nonce: 0,
            deadline: 0
        });

        _mockExpectCall(
            PERMIT2,
            abi.encodeWithSelector(
                bytes4(0x137c29fe),
                makerPermit,
                ISignatureTransfer.SignatureTransferDetails({to: RECIPIENT, requestedAmount: amount}),
                MAKER,
                bytes32(0x30fd0fb242892788e98ff4323f8e366b5f1dd9a4c033f5ea6ae4252f6e887e37), /* witness */
                "Consideration consideration)Consideration(address token,uint256 amount,address counterparty,bool partialFillAllowed)TokenPermissions(address token,uint256 amount)",
                hex"dead"
            ),
            new bytes(0)
        );

        _mockExpectCall(
            address(TOKEN0), abi.encodeWithSelector(IERC20.balanceOf.selector, address(otc)), abi.encode(amount)
        );

        _mockExpectCall(
            address(TOKEN0), abi.encodeWithSelector(IERC20.transfer.selector, MAKER, amount), abi.encode(true)
        );

        // Broken usage of OtcOrderSettlement.OtcOrderFilled in 0.8.21
        //      https://github.com/foundry-rs/foundry/issues/6206
        // vm.expectEmit(address(otc));
        // emit OtcOrderSettlement.OtcOrderFilled(
        //     bytes32(0x33d473fdc5cd07e2f752b882bb4f51ccc88c742aa085ebdcbd4af689aba7ffd4),
        //     MAKER,
        //     address(this),
        //     TOKEN1,
        //     TOKEN0,
        //     amount,
        //     amount
        // );

        otc.fillOtcOrderSelf(RECIPIENT, makerPermit, MAKER, hex"dead", TOKEN0, amount, address(this));
    }

    function testOtcMetaTxn() public {
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

        // Maker payment via Permit2
        _mockExpectCall(
            PERMIT2,
            abi.encodeWithSelector(
                bytes4(0x137c29fe),
                makerPermit,
                ISignatureTransfer.SignatureTransferDetails({to: RECIPIENT, requestedAmount: amount}),
                MAKER,
                bytes32(0x315954c1f9717c9d14604de3c6ceb9fd601b3bd1d0b8ec397e8c2b81668a02e1), /* witness */
                otc.considerationWitnessType(),
                hex"dead"
            ),
            new bytes(0)
        );

        // Taker payment via Permit2
        _mockExpectCall(
            PERMIT2,
            abi.encodeWithSelector(
                bytes4(0x137c29fe),
                takerPermit,
                ISignatureTransfer.SignatureTransferDetails({to: MAKER, requestedAmount: amount}),
                address(this), /* taker */
                bytes32(0x0000000000000000000000000000000000000000000000000000000000000000), /* witness */
                otc.actionsAndSlippageWitnessType(),
                hex"beef"
            ),
            new bytes(0)
        );

        // Broken usage of OtcOrderSettlement.OtcOrderFilled in 0.8.21
        //      https://github.com/foundry-rs/foundry/issues/6206
        // vm.expectEmit(address(otc));
        // emit OtcOrderSettlement.OtcOrderFilled(
        //     bytes32(0xbee0e2de3e64ecfe06fe7118215a033ac40a8d6a508d60b81cd9ac6addd6e11e),
        //     MAKER,
        //     address(this),
        //     TOKEN1,
        //     TOKEN0,
        //     amount,
        //     amount
        // );

        otc.fillOtcOrderMeta(
            RECIPIENT, makerPermit, MAKER, hex"dead", takerPermit, address(this), hex"beef", bytes32(0x00)
        );
    }
}

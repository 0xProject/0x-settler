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
                "Consideration consideration)Consideration(address token,uint256 amount,address counterparty,bool partialFillAllowed)TokenPermissions(address token,uint256 amount)",
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

    function testOtcDirectCounterpartiesAllowanceHolder() public {
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
                "Consideration consideration)Consideration(address token,uint256 amount,address counterparty,bool partialFillAllowed)TokenPermissions(address token,uint256 amount)",
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
        address(otc).call(
            abi.encodePacked(
                abi.encodeCall(
                    otc.fillOtcOrderDirectCounterparties, (RECIPIENT, makerPermit, MAKER, hex"dead", takerPermit, hex"")
                ),
                address(this)
            ) // Forward on true msg.sender
        );
    }
}

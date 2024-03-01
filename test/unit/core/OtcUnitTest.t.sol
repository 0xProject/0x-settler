// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {OtcOrderSettlement} from "src/core/OtcOrderSettlement.sol";
import {Permit2Payment} from "src/core/Permit2Payment.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {IAllowanceHolder} from "src/allowanceholder/IAllowanceHolder.sol";

import {Utils} from "../Utils.sol";
import {IERC20} from "../../../src/IERC20.sol";

import {Test} from "forge-std/Test.sol";

contract OtcOrderSettlementDummy is OtcOrderSettlement, Permit2Payment {
    constructor(address permit2, address allowanceHolder) Permit2Payment(permit2, allowanceHolder) {}

    function considerationWitnessType() external pure returns (string memory) {
        return CONSIDERATION_WITNESS;
    }

    function actionsAndSlippageWitnessType() external pure returns (string memory) {
        return string(
            abi.encodePacked(
                "ActionsAndSlippage actionsAndSlippage)", ACTIONS_AND_SLIPPAGE_TYPE, TOKEN_PERMISSIONS_TYPE
            )
        );
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
        _setWitness(takerWitness);
        super.fillOtcOrderMetaTxn(recipient, makerPermit, maker, makerSig, takerPermit, taker, takerSig);
    }
}

contract OtcUnitTest is Utils, Test {
    OtcOrderSettlementDummy otc;
    address PERMIT2 = _createNamedRejectionDummy("PERMIT2");
    address ALLOWANCE_HOLDER = _createNamedRejectionDummy("ALLOWANCE_HOLDER");

    address TOKEN0 = _createNamedRejectionDummy("TOKEN0");
    address TOKEN1 = _createNamedRejectionDummy("TOKEN1");
    address RECIPIENT = _createNamedRejectionDummy("RECIPIENT");
    address MAKER = _createNamedRejectionDummy("MAKER");

    function setUp() public {
        otc = new OtcOrderSettlementDummy(PERMIT2, ALLOWANCE_HOLDER);
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

        _mockExpectCall(
            PERMIT2,
            abi.encodeWithSelector(
                bytes4(0x137c29fe),
                makerPermit,
                transferDetails,
                MAKER,
                witness,
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
        _mockExpectCall(
            PERMIT2,
            abi.encodeWithSelector(
                bytes4(0x137c29fe),
                makerPermit,
                transferDetails,
                MAKER,
                witness,
                otc.considerationWitnessType(),
                hex"dead"
            ),
            new bytes(0)
        );

        _mockExpectCall(
            ALLOWANCE_HOLDER,
            abi.encodeCall(IAllowanceHolder.transferFrom, (TOKEN0, address(this), MAKER, amount)),
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

        _mockExpectCall(
            PERMIT2,
            abi.encodeWithSelector(
                bytes4(0x137c29fe),
                makerPermit,
                transferDetails,
                MAKER,
                witness,
                otc.considerationWitnessType(),
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
        _mockExpectCall(
            PERMIT2,
            abi.encodeWithSelector(
                bytes4(0x137c29fe),
                makerPermit,
                transferDetails,
                MAKER,
                witness,
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

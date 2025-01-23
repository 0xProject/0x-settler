// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {SafeTransferLib} from "src/vendor/SafeTransferLib.sol";

import {BasePairTest} from "./BasePairTest.t.sol";

abstract contract Permit2TransferTest is BasePairTest {
    using SafeTransferLib for IERC20;

    function setUp() public virtual override {
        super.setUp();
        safeApproveIfBelow(fromToken(), FROM, address(PERMIT2), amount());
        warmPermit2Nonce(FROM);
    }

    // function testPermit2_permitTransferFrom() public {
    //     ISignatureTransfer.PermitBatchTransferFrom memory permit =
    //         defaultERC20PermitTransfer(address(fromToken()), amount(), 1);
    //     bytes memory sig =
    //         getPermitTransferSignature(permit, address(this), FROM_PRIVATE_KEY, permit2Domain);
    //     ISignatureTransfer.SignatureTransferDetails memory transferDetails = ISignatureTransfer.SignatureTransferDetails({
    //         to: address(BURN_ADDRESS),
    //         requestedAmount: permit.permitted.amount
    //     });

    //     snapStartName("permit2_permitTransferFrom_coldNonce");
    //     PERMIT2.permitTransferFrom(permit, transferDetails, FROM, sig);
    //     snapEnd();
    // }

    function testPermit2_permitTransferFrom_warmNonce() public {
        ISignatureTransfer.PermitBatchTransferFrom memory permit =
            defaultERC20PermitBatchTransfer(address(fromToken()), amount(), 1);
        bytes memory sig = getPermitTransferSignature(permit, address(this), FROM_PRIVATE_KEY, permit2Domain);
        ISignatureTransfer.SignatureTransferDetails[] memory transferDetails =
            new ISignatureTransfer.SignatureTransferDetails[](1);
        transferDetails[0] = ISignatureTransfer.SignatureTransferDetails({
            to: address(BURN_ADDRESS),
            requestedAmount: permit.permitted[0].amount
        });

        snapStartName("permit2_permitTransferFrom_warmNonce");
        PERMIT2.permitTransferFrom(permit, transferDetails, FROM, sig);
        snapEnd();
    }

    struct MockWitness {
        address person;
    }

    bytes32 private constant FULL_MOCK_WITNESS_TYPEHASH = keccak256(
        "PermitBatchWitnessTransferFrom(TokenPermissions[] permitted,address spender,uint256 nonce,uint256 deadline,MockWitness witness)MockWitness(address person)TokenPermissions(address token,uint256 amount)"
    );
    string private constant WITNESS_TYPE_STRING =
        "MockWitness witness)MockWitness(address person)TokenPermissions(address token,uint256 amount)";

    function testPermit2_permitWitnessTransferFrom_warmNonce() public {
        MockWitness memory witnessData = MockWitness(address(1));
        bytes32 witness = keccak256(abi.encode(witnessData));

        ISignatureTransfer.PermitBatchTransferFrom memory permit =
            defaultERC20PermitBatchTransfer(address(fromToken()), amount(), 1);
        bytes memory sig = getPermitWitnessTransferSignature(
            permit, address(this), FROM_PRIVATE_KEY, FULL_MOCK_WITNESS_TYPEHASH, witness, permit2Domain
        );
        ISignatureTransfer.SignatureTransferDetails[] memory transferDetails =
            new ISignatureTransfer.SignatureTransferDetails[](1);
        transferDetails[0] = ISignatureTransfer.SignatureTransferDetails({
            to: address(BURN_ADDRESS),
            requestedAmount: permit.permitted[0].amount
        });

        snapStartName("permit2_permitWitnessTransferFrom_warmNonce");
        PERMIT2.permitWitnessTransferFrom(permit, transferDetails, FROM, witness, WITNESS_TYPE_STRING, sig);
        snapEnd();
    }
}

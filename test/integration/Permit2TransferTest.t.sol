// SPDX-License-Identifier: MIT
pragma solidity ^0.8.17;

import {BasePairTest} from "./BasePairTest.t.sol";

import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";

abstract contract Permit2TransferTest is BasePairTest {
    function testPermit2_permitTransferFrom() public {
        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken()), uint160(amount()), 0);
        bytes memory sig =
            getPermitTransferSignature(permit, address(this), FROM_PRIVATE_KEY, PERMIT2.DOMAIN_SEPARATOR());
        ISignatureTransfer.SignatureTransferDetails memory transferDetails =
            ISignatureTransfer.SignatureTransferDetails({to: address(BURN_ADDRESS), requestedAmount: permit.permitted.amount});

        deal(address(fromToken()), FROM, amount());
        vm.prank(FROM);
        fromToken().approve(address(PERMIT2), type(uint256).max);

        snapStartName("permit2_permitTransferFrom_coldNonce");
        PERMIT2.permitTransferFrom(permit, transferDetails, FROM, sig);
        snapEnd();
    }

    function testPermit2_permitTransferFrom_warmNonce() warmPermit2Nonce() public {
        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken()), uint160(amount()), 1);
        bytes memory sig =
            getPermitTransferSignature(permit, address(this), FROM_PRIVATE_KEY, PERMIT2.DOMAIN_SEPARATOR());
        ISignatureTransfer.SignatureTransferDetails memory transferDetails =
            ISignatureTransfer.SignatureTransferDetails({to: address(BURN_ADDRESS), requestedAmount: permit.permitted.amount});

        deal(address(fromToken()), FROM, amount());
        vm.prank(FROM);
        fromToken().approve(address(PERMIT2), type(uint256).max);

        snapStartName("permit2_permitTransferFrom_warmNonce");
        PERMIT2.permitTransferFrom(permit, transferDetails, FROM, sig);
        snapEnd();
    }
}

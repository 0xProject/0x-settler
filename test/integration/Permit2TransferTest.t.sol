// SPDX-License-Identifier: MIT
pragma solidity ^0.8.17;

import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {SafeTransferLib} from "solmate/src/utils/SafeTransferLib.sol";
import {ERC20} from "solmate/src/tokens/ERC20.sol";

import {BasePairTest} from "./BasePairTest.t.sol";

abstract contract Permit2TransferTest is BasePairTest {
    using SafeTransferLib for ERC20;

    function testPermit2_permitTransferFrom() public {
        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken()), uint160(amount()), 0);
        bytes memory sig =
            getPermitTransferSignature(permit, address(this), FROM_PRIVATE_KEY, PERMIT2.DOMAIN_SEPARATOR());
        ISignatureTransfer.SignatureTransferDetails memory transferDetails = ISignatureTransfer.SignatureTransferDetails({
            to: address(BURN_ADDRESS),
            requestedAmount: permit.permitted.amount
        });

        deal(address(fromToken()), FROM, amount());
        vm.prank(FROM);
        fromToken().safeApprove(address(PERMIT2), type(uint256).max);

        snapStartName("permit2_permitTransferFrom_coldNonce");
        PERMIT2.permitTransferFrom(permit, transferDetails, FROM, sig);
        snapEnd();
    }

    function testPermit2_permitTransferFrom_warmNonce() public warmPermit2Nonce {
        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken()), uint160(amount()), 1);
        bytes memory sig =
            getPermitTransferSignature(permit, address(this), FROM_PRIVATE_KEY, PERMIT2.DOMAIN_SEPARATOR());
        ISignatureTransfer.SignatureTransferDetails memory transferDetails = ISignatureTransfer.SignatureTransferDetails({
            to: address(BURN_ADDRESS),
            requestedAmount: permit.permitted.amount
        });

        deal(address(fromToken()), FROM, amount());
        vm.prank(FROM);
        fromToken().safeApprove(address(PERMIT2), type(uint256).max);

        snapStartName("permit2_permitTransferFrom_warmNonce");
        PERMIT2.permitTransferFrom(permit, transferDetails, FROM, sig);
        snapEnd();
    }
}

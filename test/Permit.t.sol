// SPDX-License-Identifier: MIT
pragma solidity ^0.8.17;

import {Test} from "forge-std/Test.sol";
import {GasSnapshot} from "forge-gas-snapshot/GasSnapshot.sol";
import {Permit2} from "permit2/src/Permit2.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {IAllowanceTransfer} from "permit2/src/interfaces/IAllowanceTransfer.sol";

import {MockERC20} from "./mocks/MockERC20.sol";
import {Permit2Signature} from "./utils/Permit2Signature.sol";

contract PermitTest is Test, Permit2Signature, GasSnapshot {
    Permit2 PERMIT2;
    MockERC20 TOKEN;

    uint256 FROM_PRIVATE_KEY = 0x1337;
    address FROM = vm.addr(FROM_PRIVATE_KEY);
    address RECIPIENT = address(0xC0ffee0c0FFEE000000000000000000000000000);
    uint160 AMOUNT = 100e18;
    uint48 EXPIRATION = uint48(block.timestamp + 1000);
    uint48 constant NONCE = 0;

    address SPENDER = address(this);

    function setUp() public {
        PERMIT2 = new Permit2();
        TOKEN = new MockERC20("MockERC20", "MERC20", 18);
        TOKEN.mint(FROM, AMOUNT);

        vm.prank(FROM);
        TOKEN.approve(address(PERMIT2), type(uint256).max);
    }

    function testPermitThenTransferFrom() public {
        uint256 startBalanceFrom = TOKEN.balanceOf(FROM);
        uint256 startBalanceTo = TOKEN.balanceOf(RECIPIENT);

        IAllowanceTransfer.PermitSingle memory permit =
            defaultERC20PermitAllowance(address(TOKEN), AMOUNT, EXPIRATION, NONCE);
        bytes memory sig = getPermitSignature(permit, FROM_PRIVATE_KEY, PERMIT2.DOMAIN_SEPARATOR());

        snapStart("permit_permit_transferFrom");
        PERMIT2.permit(FROM, permit, sig);
        PERMIT2.transferFrom(FROM, RECIPIENT, AMOUNT, address(TOKEN));
        snapEnd();

        assertEq(TOKEN.balanceOf(FROM), startBalanceFrom - AMOUNT);
        assertEq(TOKEN.balanceOf(RECIPIENT), startBalanceTo + AMOUNT);
    }

    function testPermitThenTransferFrom_split() public {
        uint256 startBalanceFrom = TOKEN.balanceOf(FROM);
        uint256 startBalanceTo = TOKEN.balanceOf(RECIPIENT);

        IAllowanceTransfer.PermitSingle memory permit =
            defaultERC20PermitAllowance(address(TOKEN), AMOUNT, EXPIRATION, NONCE);
        bytes memory sig = getPermitSignature(permit, FROM_PRIVATE_KEY, PERMIT2.DOMAIN_SEPARATOR());

        snapStart("permit_permit");
        PERMIT2.permit(FROM, permit, sig);
        snapEnd();

        (uint160 amount,,) = PERMIT2.allowance(FROM, address(TOKEN), address(this));

        assertEq(amount, AMOUNT);

        snapStart("permit_transferFrom");
        PERMIT2.transferFrom(FROM, RECIPIENT, AMOUNT, address(TOKEN));
        snapEnd();

        assertEq(TOKEN.balanceOf(FROM), startBalanceFrom - AMOUNT);
        assertEq(TOKEN.balanceOf(RECIPIENT), startBalanceTo + AMOUNT);
    }

    function testPermitTransferFrom() public {
        uint256 startBalanceFrom = TOKEN.balanceOf(FROM);
        uint256 startBalanceTo = TOKEN.balanceOf(RECIPIENT);

        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(TOKEN), AMOUNT / 2, NONCE);
        bytes memory sig = getPermitTransferSignature(permit, SPENDER, FROM_PRIVATE_KEY, PERMIT2.DOMAIN_SEPARATOR());

        ISignatureTransfer.SignatureTransferDetails memory transferDetails =
            ISignatureTransfer.SignatureTransferDetails({to: RECIPIENT, requestedAmount: AMOUNT / 2});

        snapStart("permit_permitTransferFrom_coldFrom_coldRecipient");
        PERMIT2.permitTransferFrom(permit, transferDetails, FROM, sig);
        snapEnd();

        permit = defaultERC20PermitTransfer(address(TOKEN), AMOUNT / 2, NONCE + 1);
        sig = getPermitTransferSignature(permit, SPENDER, FROM_PRIVATE_KEY, PERMIT2.DOMAIN_SEPARATOR());

        transferDetails = ISignatureTransfer.SignatureTransferDetails({to: RECIPIENT, requestedAmount: AMOUNT / 2});

        snapStart("permit_permitTransferFrom_warmFrom_warmRecipient");
        PERMIT2.permitTransferFrom(permit, transferDetails, FROM, sig);
        snapEnd();

        assertEq(TOKEN.balanceOf(FROM), startBalanceFrom - AMOUNT);
        assertEq(TOKEN.balanceOf(RECIPIENT), startBalanceTo + AMOUNT);
    }

    function testPermitTransferFrom_coldFrom_warmRecipient() public {
        // Warm up the recipient to have a token balance > 0
        TOKEN.mint(RECIPIENT, 1);
        uint256 startBalanceFrom = TOKEN.balanceOf(FROM);
        uint256 startBalanceTo = TOKEN.balanceOf(RECIPIENT);

        ISignatureTransfer.PermitTransferFrom memory permit = defaultERC20PermitTransfer(address(TOKEN), AMOUNT, NONCE);
        bytes memory sig = getPermitTransferSignature(permit, SPENDER, FROM_PRIVATE_KEY, PERMIT2.DOMAIN_SEPARATOR());

        ISignatureTransfer.SignatureTransferDetails memory transferDetails =
            ISignatureTransfer.SignatureTransferDetails({to: RECIPIENT, requestedAmount: AMOUNT});

        snapStart("permit_permitTransferFrom_coldFrom_warmRecipient");
        PERMIT2.permitTransferFrom(permit, transferDetails, FROM, sig);
        snapEnd();

        assertEq(TOKEN.balanceOf(FROM), startBalanceFrom - AMOUNT);
        assertEq(TOKEN.balanceOf(RECIPIENT), startBalanceTo + AMOUNT);
    }

    function testPermitTransferFrom_warmFrom_coldRecipient() public {
        uint256 startBalanceFrom = TOKEN.balanceOf(FROM);
        uint256 startBalanceTo = TOKEN.balanceOf(RECIPIENT);

        // Warm up the Permit2 Nonce for the FROM address
        ISignatureTransfer.PermitTransferFrom memory permit = defaultERC20PermitTransfer(address(TOKEN), AMOUNT, NONCE);
        bytes memory sig = getPermitTransferSignature(permit, SPENDER, FROM_PRIVATE_KEY, PERMIT2.DOMAIN_SEPARATOR());

        // Initialize our Permit2 nonce by burning these tokens
        ISignatureTransfer.SignatureTransferDetails memory transferDetails =
            ISignatureTransfer.SignatureTransferDetails({to: address(0), requestedAmount: AMOUNT});
        PERMIT2.permitTransferFrom(permit, transferDetails, FROM, sig);

        // Re-mint the tokens we just burned
        TOKEN.mint(FROM, AMOUNT);

        permit = defaultERC20PermitTransfer(address(TOKEN), AMOUNT, NONCE + 1);
        sig = getPermitTransferSignature(permit, SPENDER, FROM_PRIVATE_KEY, PERMIT2.DOMAIN_SEPARATOR());
        transferDetails = ISignatureTransfer.SignatureTransferDetails({to: RECIPIENT, requestedAmount: AMOUNT});

        snapStart("permit_permitTransferFrom_warmFrom_coldRecipient");
        PERMIT2.permitTransferFrom(permit, transferDetails, FROM, sig);
        snapEnd();

        assertEq(TOKEN.balanceOf(FROM), startBalanceFrom - AMOUNT);
        assertEq(TOKEN.balanceOf(RECIPIENT), startBalanceTo + AMOUNT);
    }

    function testTransferFrom_coldRecipient() public {
        vm.startPrank(address(PERMIT2));

        snapStart("erc20_transferFrom_coldRecipient");
        TOKEN.transferFrom(FROM, RECIPIENT, AMOUNT);
        snapEnd();

        TOKEN.mint(FROM, AMOUNT);
        TOKEN.mint(RECIPIENT, 1);
        snapStart("erc20_transferFrom_warmRecipient");
        TOKEN.transferFrom(FROM, RECIPIENT, AMOUNT);
        snapEnd();

        vm.stopPrank();
    }
}

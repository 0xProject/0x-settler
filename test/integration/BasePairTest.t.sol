// SPDX-License-Identifier: MIT
pragma solidity ^0.8.17;

import {Test} from "forge-std/Test.sol";
import {GasSnapshot} from "forge-gas-snapshot/GasSnapshot.sol";

import {ERC20} from "solmate/src/tokens/ERC20.sol";
import {Permit2} from "permit2/src/Permit2.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";

import {Permit2Signature} from "../utils/Permit2Signature.sol";

import {SafeTransferLib} from "../../src/utils/SafeTransferLib.sol";

abstract contract BasePairTest is Test, GasSnapshot, Permit2Signature {
    using SafeTransferLib for ERC20;

    uint256 constant FROM_PRIVATE_KEY = 0x1337;
    address FROM = vm.addr(FROM_PRIVATE_KEY);
    uint256 constant MAKER_PRIVATE_KEY = 0x0ff1c1a1;
    address MAKER = vm.addr(MAKER_PRIVATE_KEY);

    address constant BURN_ADDRESS = 0x2222222222222222222222222222222222222222;

    Permit2 constant PERMIT2 = Permit2(0x000000000022D473030F116dDEE9F6B43aC78BA3);

    function testName() internal virtual returns (string memory);
    function fromToken() internal virtual returns (ERC20);
    function toToken() internal virtual returns (ERC20);
    function amount() internal virtual returns (uint256);

    function setUp() public {
        vm.createSelectFork(vm.envString("MAINNET_RPC_URL"));
        vm.label(address(this), "FoundryTest");
        vm.label(FROM, "FROM");
    }

    function snapStartName(string memory name) internal {
        snapStart(string.concat(name, "_", testName()));
    }

    modifier warmPermit2Nonce() {
        _warmPermit2Nonce(FROM_PRIVATE_KEY, fromToken());
        _;
    }

    modifier warmUserPermit2Nonce(uint256 privKey, ERC20 token) {
        _warmPermit2Nonce(privKey, token);
        _;
    }

    modifier skipIf(bool condition) {
        if (!condition) {
            _;
        }
    }

    function _warmPermit2Nonce(uint256 privKey, ERC20 token) internal {
        dealAndApprove(vm.addr(privKey), token, amount(), address(PERMIT2));

        // Warm up by consuming the 0 nonce
        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(token), uint160(amount()), 0);
        bytes memory sig = getPermitTransferSignature(permit, address(this), privKey, PERMIT2.DOMAIN_SEPARATOR());
        ISignatureTransfer.SignatureTransferDetails memory transferDetails =
            ISignatureTransfer.SignatureTransferDetails({to: address(this), requestedAmount: permit.permitted.amount});

        PERMIT2.permitTransferFrom(permit, transferDetails, vm.addr(privKey), sig);
    }

    function dealAndApprove(ERC20 token, uint256 amount, address spender) internal {
        deal(address(token), FROM, amount);
        safeApproveIfBelow(token, FROM, spender, amount);
    }

    function dealAndApprove(address who, ERC20 token, uint256 amount, address spender) internal {
        deal(address(token), who, amount);
        safeApproveIfBelow(token, who, spender, amount);
    }

    function safeApproveIfBelow(ERC20 token, address from, address spender, uint256 amount) internal {
        // Can't use SafeTransferLib directly due to Foundry.prank not changing address(this)
        if (token.allowance(from, spender) < amount) {
            vm.startPrank(from);
            SafeTransferLib.safeApprove(token, spender, type(uint256).max);
            vm.stopPrank();
        }
    }
}

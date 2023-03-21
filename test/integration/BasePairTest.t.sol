// SPDX-License-Identifier: MIT
pragma solidity ^0.8.17;

import {Test} from "forge-std/Test.sol";
import {GasSnapshot} from "forge-gas-snapshot/GasSnapshot.sol";

import {Permit2} from "permit2/src/Permit2.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {Permit2Signature} from "../utils/Permit2Signature.sol";

import {ERC20} from "solmate/src/tokens/ERC20.sol";

abstract contract BasePairTest is Test, GasSnapshot, Permit2Signature {
    uint256 FROM_PRIVATE_KEY = 0x1337;
    address FROM = vm.addr(FROM_PRIVATE_KEY);

    Permit2 PERMIT2 = Permit2(0x000000000022D473030F116dDEE9F6B43aC78BA3);

    function testName() internal virtual returns (string memory);
    function fromToken() internal virtual returns (ERC20);
    function toToken() internal virtual returns (ERC20);
    function amount() internal virtual returns (uint256);

    function setUp() public {
        emit log_string("BasePairTest");
        vm.createSelectFork(vm.envString("MAINNET_RPC_URL"));
    }

    function snapStartName(string memory name) internal {
        snapStart(string.concat(name, "_", testName()));
    }

    modifier warmPermit2Nonce() {
        deal(address(fromToken()), FROM, amount());
        vm.prank(FROM);
        fromToken().approve(address(PERMIT2), type(uint256).max);

        // Warm up by consuming the 0 nonce
        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken()), uint160(amount()), 0);
        bytes memory sig =
            getPermitTransferSignature(permit, address(this), FROM_PRIVATE_KEY, PERMIT2.DOMAIN_SEPARATOR());
        ISignatureTransfer.SignatureTransferDetails memory transferDetails =
            ISignatureTransfer.SignatureTransferDetails({to: address(this), requestedAmount: permit.permitted.amount});

        PERMIT2.permitTransferFrom(permit, transferDetails, FROM, sig);
        _;
    }
}

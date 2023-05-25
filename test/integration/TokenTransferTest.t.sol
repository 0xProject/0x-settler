// SPDX-License-Identifier: MIT
pragma solidity ^0.8.17;

import {ERC20} from "solmate/src/tokens/ERC20.sol";

import {SafeTransferLib} from "../../src/utils/SafeTransferLib.sol";

import {BasePairTest} from "./BasePairTest.t.sol";

abstract contract TokenTransferTest is BasePairTest {
    using SafeTransferLib for ERC20;

    function setUp() public virtual override {
        super.setUp();
    }

    function testToken_transfer_entire() public {
        vm.startPrank(FROM);
        deal(address(fromToken()), FROM, amount());
        snapStartName("tokenFrom_transfer_entire");
        fromToken().safeTransfer(BURN_ADDRESS, amount());
        snapEnd();

        deal(address(toToken()), FROM, amount());
        snapStartName("tokenTo_transfer_entire");
        toToken().safeTransfer(BURN_ADDRESS, amount());
        snapEnd();
    }

    function testToken_transferFrom_entire() public {
        address spender = address(this);

        deal(address(fromToken()), FROM, amount());
        safeApproveIfBelow(fromToken(), FROM, spender, amount());
        snapStartName("tokenFrom_transferFrom_entire");
        fromToken().safeTransferFrom(FROM, BURN_ADDRESS, amount());
        snapEnd();

        deal(address(toToken()), FROM, amount());
        safeApproveIfBelow(toToken(), FROM, spender, amount());
        snapStartName("tokenTo_transferFrom_entire");
        toToken().safeTransferFrom(FROM, BURN_ADDRESS, amount());
        snapEnd();
    }

    function testToken_transfer_partial() public {
        vm.startPrank(FROM);
        deal(address(fromToken()), FROM, amount());
        snapStartName("tokenFrom_transfer_partial");
        fromToken().safeTransfer(BURN_ADDRESS, amount() / 2);
        snapEnd();

        deal(address(toToken()), FROM, amount());
        snapStartName("tokenTo_transfer_partial");
        toToken().safeTransfer(BURN_ADDRESS, amount() / 2);
        snapEnd();
    }

    function testToken_transferFrom_partial() public {
        address spender = address(this);

        deal(address(fromToken()), FROM, amount());
        safeApproveIfBelow(fromToken(), FROM, spender, amount());
        snapStartName("tokenFrom_transferFrom_partial");
        fromToken().safeTransferFrom(FROM, BURN_ADDRESS, amount() / 2);
        snapEnd();

        deal(address(toToken()), FROM, amount());
        safeApproveIfBelow(toToken(), FROM, spender, amount());
        snapStartName("tokenTo_transferFrom_partial");
        toToken().safeTransferFrom(FROM, BURN_ADDRESS, amount() / 2);
        snapEnd();
    }

    function testToken_transfer_partial_warm() public {
        deal(address(fromToken()), BURN_ADDRESS, 1);
        deal(address(toToken()), BURN_ADDRESS, 1);

        vm.startPrank(FROM);
        deal(address(fromToken()), FROM, amount());
        snapStartName("tokenFrom_transfer_partial_warmRecipient");
        fromToken().safeTransfer(BURN_ADDRESS, amount() / 2);
        snapEnd();

        deal(address(toToken()), FROM, amount());
        snapStartName("tokenTo_transfer_partial_warmRecipient");
        toToken().safeTransfer(BURN_ADDRESS, amount() / 2);
        snapEnd();
    }

    function testToken_transferFrom_partial_warm() public {
        deal(address(fromToken()), BURN_ADDRESS, 1);
        deal(address(toToken()), BURN_ADDRESS, 1);
        address spender = address(this);

        deal(address(fromToken()), FROM, amount());
        safeApproveIfBelow(fromToken(), FROM, spender, amount());
        snapStartName("tokenFrom_transferFrom_partial_warmRecipient");
        fromToken().safeTransferFrom(FROM, BURN_ADDRESS, amount() / 2);
        snapEnd();

        deal(address(toToken()), FROM, amount());
        safeApproveIfBelow(toToken(), FROM, spender, amount());
        snapStartName("tokenTo_transferFrom_partial_warmRecipient");
        toToken().safeTransferFrom(FROM, BURN_ADDRESS, amount() / 2);
        snapEnd();
    }
}

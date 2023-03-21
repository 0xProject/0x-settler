// SPDX-License-Identifier: MIT
pragma solidity ^0.8.17;

import {SafeTransferLib} from "solmate/src/utils/SafeTransferLib.sol";
import {ERC20} from "solmate/src/tokens/ERC20.sol";

import {BasePairTest} from "./BasePairTest.t.sol";

abstract contract TokenTransferTest is BasePairTest {
    using SafeTransferLib for ERC20;

    function testToken_transfer_entire() public {
        vm.startPrank(FROM);
        deal(address(fromToken()), FROM, amount());
        snapStartName("tokenFrom_transfer_entire");
        fromToken().transfer(BURN_ADDRESS, amount());
        snapEnd();

        deal(address(toToken()), FROM, amount());
        snapStartName("tokenTo_transfer_entire");
        toToken().transfer(BURN_ADDRESS, amount());
        snapEnd();
    }

    function testToken_transferFrom_entire() public {
        address spender = address(this);

        vm.startPrank(FROM);
        deal(address(fromToken()), FROM, amount());
        fromToken().safeApprove(spender, type(uint256).max);
        vm.stopPrank();
        snapStartName("tokenFrom_transferFrom_entire");
        fromToken().transferFrom(FROM, BURN_ADDRESS, amount());
        snapEnd();

        vm.startPrank(FROM);
        deal(address(toToken()), FROM, amount());
        toToken().safeApprove(spender, type(uint256).max);
        vm.stopPrank();
        snapStartName("tokenTo_transferFrom_entire");
        toToken().transferFrom(FROM, BURN_ADDRESS, amount());
        snapEnd();
    }

    function testToken_transfer_partial() public {
        vm.startPrank(FROM);
        deal(address(fromToken()), FROM, amount());
        snapStartName("tokenFrom_transfer_partial");
        fromToken().transfer(BURN_ADDRESS, amount() / 2);
        snapEnd();

        deal(address(toToken()), FROM, amount());
        snapStartName("tokenTo_transfer_partial");
        toToken().transfer(BURN_ADDRESS, amount() / 2);
        snapEnd();
    }

    function testToken_transferFrom_partial() public {
        address spender = address(this);

        vm.startPrank(FROM);
        deal(address(fromToken()), FROM, amount());
        fromToken().safeApprove(spender, type(uint256).max);
        vm.stopPrank();
        snapStartName("tokenFrom_transferFrom_partial");
        fromToken().transferFrom(FROM, BURN_ADDRESS, amount() / 2);
        snapEnd();

        vm.startPrank(FROM);
        deal(address(toToken()), FROM, amount());
        toToken().safeApprove(spender, type(uint256).max);
        vm.stopPrank();
        snapStartName("tokenTo_transferFrom_partial");
        toToken().transferFrom(FROM, BURN_ADDRESS, amount() / 2);
        snapEnd();
    }

    function testToken_transfer_partial_warm() public {
        deal(address(fromToken()), BURN_ADDRESS, 1);
        deal(address(toToken()), BURN_ADDRESS, 1);

        vm.startPrank(FROM);
        deal(address(fromToken()), FROM, amount());
        snapStartName("tokenFrom_transfer_partial_warmRecipient");
        fromToken().transfer(BURN_ADDRESS, amount() / 2);
        snapEnd();

        deal(address(toToken()), FROM, amount());
        snapStartName("tokenTo_transfer_partial_warmRecipient");
        toToken().transfer(BURN_ADDRESS, amount() / 2);
        snapEnd();
    }

    function testToken_transferFrom_partial_warm() public {
        deal(address(fromToken()), BURN_ADDRESS, 1);
        deal(address(toToken()), BURN_ADDRESS, 1);
        address spender = address(this);

        vm.startPrank(FROM);
        deal(address(fromToken()), FROM, amount());
        fromToken().safeApprove(spender, type(uint256).max);
        vm.stopPrank();
        snapStartName("tokenFrom_transferFrom_partial_warmRecipient");
        fromToken().transferFrom(FROM, BURN_ADDRESS, amount() / 2);
        snapEnd();

        vm.startPrank(FROM);
        deal(address(toToken()), FROM, amount());
        toToken().safeApprove(spender, type(uint256).max);
        vm.stopPrank();
        snapStartName("tokenTo_transferFrom_partial_warmRecipient");
        toToken().transferFrom(FROM, BURN_ADDRESS, amount() / 2);
        snapEnd();
    }
}

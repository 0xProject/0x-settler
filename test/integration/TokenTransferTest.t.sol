// SPDX-License-Identifier: MIT
pragma solidity ^0.8.17;

import {BasePairTest} from "./BasePairTest.t.sol";

abstract contract TokenTransferTest is BasePairTest {
    address BURN_ADDRESS = 0x2222222222222222222222222222222222222222;

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
        fromToken().approve(spender, type(uint256).max);
        vm.stopPrank();
        snapStartName("tokenFrom_transferFrom_entire");
        fromToken().transferFrom(FROM, BURN_ADDRESS, amount());
        snapEnd();

        vm.startPrank(FROM);
        deal(address(toToken()), FROM, amount());
        toToken().approve(spender, type(uint256).max);
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
        fromToken().approve(spender, type(uint256).max);
        vm.stopPrank();
        snapStartName("tokenFrom_transferFrom_partial");
        fromToken().transferFrom(FROM, BURN_ADDRESS, amount() / 2);
        snapEnd();

        vm.startPrank(FROM);
        deal(address(toToken()), FROM, amount());
        toToken().approve(spender, type(uint256).max);
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
        snapStartName("tokenFrom_transfer_partial_warm");
        fromToken().transfer(BURN_ADDRESS, amount() / 2);
        snapEnd();

        deal(address(toToken()), FROM, amount());
        snapStartName("tokenTo_transfer_partial_warm");
        toToken().transfer(BURN_ADDRESS, amount() / 2);
        snapEnd();
    }

    function testToken_transferFrom_partial_warm() public {
        deal(address(fromToken()), BURN_ADDRESS, 1);
        deal(address(toToken()), BURN_ADDRESS, 1);
        address spender = address(this);

        vm.startPrank(FROM);
        deal(address(fromToken()), FROM, amount());
        fromToken().approve(spender, type(uint256).max);
        vm.stopPrank();
        snapStartName("tokenFrom_transferFrom_partial_warm");
        fromToken().transferFrom(FROM, BURN_ADDRESS, amount() / 2);
        snapEnd();

        vm.startPrank(FROM);
        deal(address(toToken()), FROM, amount());
        toToken().approve(spender, type(uint256).max);
        vm.stopPrank();
        snapStartName("tokenTo_transferFrom_partial_warm");
        toToken().transferFrom(FROM, BURN_ADDRESS, amount() / 2);
        snapEnd();
    }
}

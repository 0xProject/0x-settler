// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {SafeTransferLib} from "src/vendor/SafeTransferLib.sol";

import {BasePairTest} from "./BasePairTest.t.sol";

abstract contract TokenTransferTest is BasePairTest {
    using SafeTransferLib for IERC20;

    function setUp() public virtual override {
        super.setUp();
    }

    function testToken_transfer_entire() public {
        vm.startPrank(FROM);
        deal(address(fromToken()), FROM, amount());
        fromToken().safeTransfer(BURN_ADDRESS, amount());

        deal(address(toToken()), FROM, amount());
        toToken().safeTransfer(BURN_ADDRESS, amount());
    }

    function testToken_transferFrom_entire() public {
        address spender = address(this);

        deal(address(fromToken()), FROM, amount());
        safeApproveIfBelow(fromToken(), FROM, spender, amount());
        fromToken().safeTransferFrom(FROM, BURN_ADDRESS, amount());

        deal(address(toToken()), FROM, amount());
        safeApproveIfBelow(toToken(), FROM, spender, amount());
        toToken().safeTransferFrom(FROM, BURN_ADDRESS, amount());
    }
}

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "@forge-std/Test.sol";
import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {ALLOWANCE_HOLDER} from "src/allowanceholder/IAllowanceHolder.sol";
import {PERMIT2} from "src/core/Permit2Payment.sol";

import {IMsgSender} from "src/interfaces/IMsgSender.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {BaseSettler} from "src/chains/Base/TakerSubmitted.sol";

contract MsgSenderUnitTest is Test {
    BaseSettler internal settler;
    MsgSenderCallbackHelper internal callbackHelper;

    function setUp() public {
        settler = new BaseSettler(bytes20(0));
        callbackHelper = new MsgSenderCallbackHelper();
    }

    function test_msgSender_TakerSubmitted_RevertsWhenNoPayerSet() public {
        vm.expectRevert(new bytes(0));
        IMsgSender(address(settler)).msgSender();
    }

    function test_msgSender_TakerSubmitted_ReturnsPayerDuringExecution() public {
        address testPayer = makeAddr("testPayer");

        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeCall(
            ISettlerActions.BASIC,
            (
                address(0), // sellToken (no token transfer needed)
                0, // bps
                address(callbackHelper), // pool (our callback helper)
                0, // offset
                abi.encodeCall(MsgSenderCallbackHelper.checkMsgSender, (address(settler))) // data
            )
        );

        vm.prank(testPayer, testPayer);
        settler.execute(
            ISettlerBase.AllowedSlippage({
                recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0
            }),
            actions,
            bytes32(0)
        );

        assertEq(callbackHelper.lastMsgSender(), testPayer, "msgSender should return the payer during execution");
    }

    function testFuzz_msgSender_TakerSubmitted_ReturnsCorrectPayer(address payer) public {
        vm.assume(payer != address(0));
        vm.assume(payer.code.length == 0);
        vm.assume(payer != address(ALLOWANCE_HOLDER));
        vm.assume(payer != address(PERMIT2));

        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeCall(
            ISettlerActions.BASIC,
            (
                address(0),
                0,
                address(callbackHelper),
                0,
                abi.encodeCall(MsgSenderCallbackHelper.checkMsgSender, (address(settler)))
            )
        );

        vm.prank(payer, payer);
        settler.execute(
            ISettlerBase.AllowedSlippage({
                recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0
            }),
            actions,
            bytes32(0)
        );

        assertEq(callbackHelper.lastMsgSender(), payer, "msgSender should return the fuzzed payer");
    }
}

contract MsgSenderCallbackHelper {
    address public lastMsgSender;

    function checkMsgSender(address settler) external {
        lastMsgSender = IMsgSender(settler).msgSender();
    }
}

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {BridgeSettlerIntegrationTest} from "./BridgeSettler.t.sol";
import {ALLOWANCE_HOLDER} from "src/allowanceholder/IAllowanceHolder.sol";
import {IBridgeSettlerActions} from "src/bridge/IBridgeSettlerActions.sol";
import {ArbitrumBridgeSettler} from "src/chains/Arbitrum/BridgeSettler.sol";
import {IStargateV2, IOFT, ETH} from "src/core/StargateV2.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";
import {LibBytes} from "../utils/LibBytes.sol";

contract StargateV2Test is BridgeSettlerIntegrationTest {
    using LibBytes for bytes;

    address pool;

    receive() external payable {}

    function _testBridgeSettler() internal override {
        bridgeSettler = new ArbitrumBridgeSettler(bytes20(0));
    }

    function _prepareSendToken(uint256 amount)
        internal
        returns (IOFT.SendParam memory sendParam, IOFT.MessagingFee memory messagingFee, uint256 fee)
    {
        sendParam = IOFT.SendParam({
            dstEid: uint32(30110), // ARBITRUM
            to: bytes32(uint256(uint160(makeAddr("recipient")))),
            amountLD: amount,
            minAmountLD: amount,
            extraOptions: bytes(""),
            composeMsg: bytes(""),
            oftCmd: bytes("") // TAXI mode
        });

        (,, IOFT.OFTReceipt memory receipt) = IOFT(pool).quoteOFT(sendParam);
        sendParam.minAmountLD = receipt.amountReceivedLD;

        messagingFee = IOFT(pool).quoteSend(sendParam, false);
        fee = messagingFee.nativeFee;
    }

    function testBridgeNative() public {
        // native pool
        pool = 0x77b2043768d28E9C9aB44E1aBfC95944bcE57931;
        uint256 amount = 1 ether;

        (IOFT.SendParam memory sendParam, IOFT.MessagingFee memory messagingFee, uint256 fee) =
            _prepareSendToken(amount);

        sendParam.amountLD = 0; // send 0 to let settler inject the value
        bytes[] memory bridgeActions = ActionDataBuilder.build(
            abi.encodeCall(
                IBridgeSettlerActions.BRIDGE_TO_STARGATE_V2,
                (address(ETH), pool, abi.encode(sendParam, messagingFee, address(this)))
            )
        );
        uint256 excess = 10;
        sendParam.amountLD = amount + excess;

        deal(address(bridgeSettler), excess);
        deal(address(this), amount + fee);
        uint256 balanceBefore = address(pool).balance;
        vm.expectCall(
            pool, amount + excess + fee, abi.encodeCall(IStargateV2.sendToken, (sendParam, messagingFee, address(this)))
        );
        bridgeSettler.execute{value: amount + fee}(bridgeActions, bytes32(0));
        uint256 balanceAfter = address(pool).balance;

        assertEq(balanceAfter - balanceBefore, amount, "Assets were not received");
        assertEq(address(this).balance, excess, "Excess was not returned");
    }

    function testBridgeERC20() public {
        // USDC pool
        pool = 0xc026395860Db2d07ee33e05fE50ed7bD583189C7;
        token = IERC20(0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48);
        uint256 amount = 10000;

        deal(address(token), address(this), amount);
        token.approve(address(ALLOWANCE_HOLDER), amount);

        (IOFT.SendParam memory sendParam, IOFT.MessagingFee memory messagingFee, uint256 fee) =
            _prepareSendToken(amount);

        sendParam.amountLD = 0; // send 0 to let settler inject the value
        bytes[] memory bridgeActions = ActionDataBuilder.build(
            _getDefaultTransferFrom(address(token), amount),
            abi.encodeCall(
                IBridgeSettlerActions.BRIDGE_TO_STARGATE_V2,
                (address(token), pool, abi.encode(sendParam, messagingFee, address(this)))
            )
        );
        sendParam.amountLD = amount;

        deal(address(this), fee);
        uint256 balanceBefore = token.balanceOf(pool);
        vm.expectCall(pool, fee, abi.encodeCall(IStargateV2.sendToken, (sendParam, messagingFee, address(this))));
        ALLOWANCE_HOLDER.exec{value: fee}(
            address(bridgeSettler),
            address(token),
            amount,
            payable(address(bridgeSettler)),
            abi.encodeCall(bridgeSettler.execute, (bridgeActions, bytes32(0)))
        );
        uint256 balanceAfter = token.balanceOf(pool);

        assertEq(balanceAfter - balanceBefore, amount, "Assets were not received");
    }
}

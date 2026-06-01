// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {BridgeSettlerIntegrationTest} from "./BridgeSettler.t.sol";
import {ALLOWANCE_HOLDER} from "src/allowanceholder/IAllowanceHolder.sol";
import {IBridgeSettlerActions} from "src/bridge/IBridgeSettlerActions.sol";
import {SafeTransferLib} from "src/vendor/SafeTransferLib.sol";
import {IOFT, ETH} from "src/core/LayerZeroOFT.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";
import {LibBytes} from "../utils/LibBytes.sol";

contract LayerZeroOFTEthereumTest is BridgeSettlerIntegrationTest {
    using SafeTransferLib for IERC20;
    using LibBytes for bytes;

    // USDT0 OFTAdapter
    address oft = 0x6C96dE32CEa08842dcc4058c14d3aaAD7Fa41dee;
    IERC20 USDT = IERC20(0xdAC17F958D2ee523a2206206994597C13D831ec7);

    receive() external payable {}

    function testBridgeERC20() public {
        uint256 amount = 10000000;
        deal(address(USDT), address(this), amount, true);
        USDT.safeApprove(address(ALLOWANCE_HOLDER), amount);

        IOFT.SendParam memory sendParam = IOFT.SendParam({
            dstEid: uint32(30110), // ARBITRUM
            to: bytes32(uint256(uint160(makeAddr("recipient")))),
            amountLD: amount,
            minAmountLD: amount,
            extraOptions: bytes(""),
            composeMsg: bytes(""),
            oftCmd: bytes("")
        });

        (,, IOFT.OFTReceipt memory receipt) = IOFT(oft).quoteOFT(sendParam);
        sendParam.minAmountLD = receipt.amountReceivedLD;

        IOFT.MessagingFee memory messagingFee = IOFT(oft).quoteSend(sendParam, false);
        uint256 fee = messagingFee.nativeFee;

        sendParam.amountLD = 0; // send 0 to let settler inject the value
        bytes[] memory bridgeActions = ActionDataBuilder.build(
            _getDefaultTransferFrom(address(USDT), amount),
            abi.encodeCall(
                IBridgeSettlerActions.BRIDGE_TO_LAYER_ZERO_OFT,
                (address(USDT), oft, abi.encodeCall(IOFT.send, (sendParam, messagingFee, address(this))).popSelector())
            )
        );
        sendParam.amountLD = amount;

        deal(address(this), fee);
        uint256 balanceBefore = USDT.balanceOf(oft);
        vm.expectCall(oft, fee, abi.encodeCall(IOFT.send, (sendParam, messagingFee, address(this))));
        ALLOWANCE_HOLDER.exec{value: fee}(
            address(bridgeSettler),
            address(USDT),
            amount,
            payable(address(bridgeSettler)),
            abi.encodeCall(bridgeSettler.execute, (bridgeActions, bytes32(0)))
        );
        uint256 balanceAfter = USDT.balanceOf(oft);

        assertEq(balanceAfter - balanceBefore, amount, "Assets were not received");
    }
}


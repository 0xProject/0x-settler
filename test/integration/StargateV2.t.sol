// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {BridgeSettlerIntegrationTest} from "./BridgeSettler.t.sol";
import {ALLOWANCE_HOLDER} from "src/allowanceholder/IAllowanceHolder.sol";
import {IBridgeSettlerActions} from "src/bridge/IBridgeSettlerActions.sol";
import {ArbitrumBridgeSettler} from "src/chains/Arbitrum/BridgeSettler.sol";

interface IStargateV2 {
    event OFTSent(
        bytes32 indexed guid, uint32 dstEid, address indexed fromAddress, uint256 amountSentLD, uint256 amountReceivedLD
    );

    struct SendParam {
        uint32 dstEid;
        bytes32 to;
        uint256 amountLD;
        uint256 minAmountLD;
        bytes extraOptions;
        bytes composeMsg;
        bytes oftCmd;
    }

    struct MessagingFee {
        uint256 nativeFee;
        uint256 lzTokenFee;
    }

    struct OFTLimit {
        uint256 minAmountLD;
        uint256 maxAmountLD;
    }

    struct OFTReceipt {
        uint256 amountSentLD;
        uint256 amountReceivedLD;
    }

    struct OFTFeeDetail {
        int256 feeAmountLD;
        string description;
    }

    function sendToken(SendParam memory SendParam, MessagingFee memory messagingFee, address refundAddress) external;

    function quoteOFT(SendParam calldata _sendParam)
        external
        view
        returns (OFTLimit memory, OFTFeeDetail[] memory oftFeeDetails, OFTReceipt memory);

    function quoteSend(SendParam calldata _sendParam, bool _payInLzToken) external view returns (MessagingFee memory);
}

contract StargateV2Test is BridgeSettlerIntegrationTest {
    address pool;

    receive() external payable {}

    function _testBridgeSettler() internal override {
        bridgeSettler = new ArbitrumBridgeSettler(bytes20(0));
    }

    function _prepareSendToken(uint256 amount)
        internal
        returns (IStargateV2.SendParam memory sendParam, IStargateV2.MessagingFee memory messagingFee, uint256 fee)
    {
        sendParam = IStargateV2.SendParam({
            dstEid: uint32(30110), // ARBITRUM
            to: bytes32(uint256(uint160(makeAddr("recipient")))),
            amountLD: amount,
            minAmountLD: amount,
            extraOptions: bytes(""),
            composeMsg: bytes(""),
            oftCmd: bytes("") // TAXI mode
        });

        (,, IStargateV2.OFTReceipt memory receipt) = IStargateV2(pool).quoteOFT(sendParam);
        sendParam.minAmountLD = receipt.amountReceivedLD;

        messagingFee = IStargateV2(pool).quoteSend(sendParam, false);
        fee = messagingFee.nativeFee;
    }

    function testBridgeNative() public {
        // native pool
        pool = 0x77b2043768d28E9C9aB44E1aBfC95944bcE57931;
        uint256 amount = 1 ether;
        uint256 extraGas = 10;

        (IStargateV2.SendParam memory sendParam, IStargateV2.MessagingFee memory messagingFee, uint256 fee) =
            _prepareSendToken(amount);

        sendParam.amountLD = 0; // send 0 to let settler inject the value
        bytes[] memory bridgeActions = new bytes[](1);
        bridgeActions[0] = abi.encodeCall(
            IBridgeSettlerActions.BRIDGE_NATIVE_TO_STARGATE_V2,
            (pool, extraGas, abi.encode(sendParam, messagingFee, address(this)))
        );
        sendParam.amountLD = amount;

        deal(address(this), amount + extraGas + fee);
        uint256 balanceBefore = address(pool).balance;
        vm.expectCall(
            pool,
            amount + extraGas + fee,
            abi.encodeCall(IStargateV2.sendToken, (sendParam, messagingFee, address(this)))
        );
        bridgeSettler.execute{value: amount + extraGas + fee}(bridgeActions, bytes32(0));
        uint256 balanceAfter = address(pool).balance;

        assertEq(balanceAfter - balanceBefore, amount, "Assets were not received");
        assertEq(address(this).balance, extraGas, "ExtraGas was not returned");
    }

    function testBridgeERC20() public {
        // USDC pool
        pool = 0xc026395860Db2d07ee33e05fE50ed7bD583189C7;
        token = IERC20(0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48);
        uint256 amount = 10000;

        deal(address(token), address(this), amount);
        token.approve(address(ALLOWANCE_HOLDER), amount);

        (IStargateV2.SendParam memory sendParam, IStargateV2.MessagingFee memory messagingFee, uint256 fee) =
            _prepareSendToken(amount);

        bytes[] memory bridgeActions = new bytes[](2);
        bridgeActions[0] = abi.encodeCall(
            IBridgeSettlerActions.TRANSFER_FROM,
            (
                address(bridgeSettler),
                ISignatureTransfer.PermitTransferFrom({
                    permitted: ISignatureTransfer.TokenPermissions({token: address(token), amount: amount}),
                    nonce: 0,
                    deadline: block.timestamp
                }),
                bytes("")
            )
        );
        sendParam.amountLD = 0; // send 0 to let settler inject the value
        bridgeActions[1] = abi.encodeCall(
            IBridgeSettlerActions.BRIDGE_ERC20_TO_STARGATE_V2,
            (address(token), pool, abi.encode(sendParam, messagingFee, address(this)))
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

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {BridgeSettlerIntegrationTest} from "./BridgeSettler.t.sol";
import {ALLOWANCE_HOLDER} from "src/allowanceholder/IAllowanceHolder.sol";
import {IBridgeSettlerActions} from "src/bridge/IBridgeSettlerActions.sol";
import {PlasmaBridgeSettler} from "src/chains/Plasma/BridgeSettler.sol";
import {SafeTransferLib} from "src/vendor/SafeTransferLib.sol";

interface IOFT {
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

    function send(SendParam memory sendParam, MessagingFee memory messagingFee, address refundAddress) external;

    function quoteOFT(SendParam calldata sendParam)
        external
        view
        returns (OFTLimit memory, OFTFeeDetail[] memory oftFeeDetails, OFTReceipt memory);

    function quoteSend(SendParam calldata sendParam, bool payInLzToken) external view returns (MessagingFee memory);
}

contract LayerZeroOFTEthereumTest is BridgeSettlerIntegrationTest {
    using SafeTransferLib for IERC20;

    // USDT0 OFTAdapter
    address oft = 0x6C96dE32CEa08842dcc4058c14d3aaAD7Fa41dee;

    receive() external payable {}

    function testBridgeERC20() public {
        // USDT
        token = IERC20(0xdAC17F958D2ee523a2206206994597C13D831ec7);
        uint256 amount = 10000000;
        deal(address(token), address(this), amount, true);
        token.safeApprove(address(ALLOWANCE_HOLDER), amount);

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
            IBridgeSettlerActions.BRIDGE_TO_LAYER_ZERO_OFT,
            (address(token), fee, oft, abi.encode(sendParam, messagingFee, address(this)))
        );
        sendParam.amountLD = amount;

        deal(address(this), fee);
        uint256 balanceBefore = token.balanceOf(oft);
        vm.expectCall(oft, fee, abi.encodeCall(IOFT.send, (sendParam, messagingFee, address(this))));
        ALLOWANCE_HOLDER.exec{value: fee}(
            address(bridgeSettler),
            address(token),
            amount,
            payable(address(bridgeSettler)),
            abi.encodeCall(bridgeSettler.execute, (bridgeActions, bytes32(0)))
        );
        uint256 balanceAfter = token.balanceOf(oft);

        assertEq(balanceAfter - balanceBefore, amount, "Assets were not received");
    }
}

contract LayerZeroOFTPlasmaTest is BridgeSettlerIntegrationTest {
    using SafeTransferLib for IERC20;

    // XPL NativeOFTAdapter
    address oft = 0x405FBc9004D857903bFD6b3357792D71a50726b0;

    function setUp() public override {
        super.setUp();
        token = IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE);
    }

    receive() external payable {}

    function _testBridgeSettler() internal virtual override {
        bridgeSettler = new PlasmaBridgeSettler(bytes20(0));
    }

    function _testChainId() internal pure override returns (string memory) {
        return "plasma";
    }

    function _testBlockNumber() internal pure override returns (uint256) {
        return 3259177;
    }

    function testBridgeNative() public {
        uint256 amount = 10 ether;

        IOFT.SendParam memory sendParam = IOFT.SendParam({
            dstEid: uint32(30102), // BNB
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
        bytes[] memory bridgeActions = new bytes[](1);
        bridgeActions[0] = abi.encodeCall(
            IBridgeSettlerActions.BRIDGE_TO_LAYER_ZERO_OFT,
            (address(token), fee, oft, abi.encode(sendParam, messagingFee, address(this)))
        );
        sendParam.amountLD = amount;

        deal(address(this), amount + fee);
        uint256 balanceBefore = address(oft).balance;
        vm.expectCall(oft, amount + fee, abi.encodeCall(IOFT.send, (sendParam, messagingFee, address(this))));
        bridgeSettler.execute{value: amount + fee}(bridgeActions, bytes32(0));
        uint256 balanceAfter = address(oft).balance;

        assertEq(balanceAfter - balanceBefore, amount, "Assets were not received");
    }

    function testBridgeNativeWithDust() public {
        uint256 dust = 1000;
        uint256 amount = 10 ether + dust;

        IOFT.SendParam memory sendParam = IOFT.SendParam({
            dstEid: uint32(30102), // BNB
            to: bytes32(uint256(uint160(makeAddr("recipient")))),
            amountLD: amount,
            minAmountLD: amount - dust,
            extraOptions: bytes(""),
            composeMsg: bytes(""),
            oftCmd: bytes("")
        });

        (,, IOFT.OFTReceipt memory receipt) = IOFT(oft).quoteOFT(sendParam);
        sendParam.minAmountLD = receipt.amountReceivedLD;

        IOFT.MessagingFee memory messagingFee = IOFT(oft).quoteSend(sendParam, false);
        uint256 fee = messagingFee.nativeFee;

        sendParam.amountLD = 0; // send 0 to let settler inject the value
        bytes[] memory bridgeActions = new bytes[](2);
        bridgeActions[0] = abi.encodeCall(
            IBridgeSettlerActions.BRIDGE_TO_LAYER_ZERO_OFT,
            (address(token), fee, oft, abi.encode(sendParam, messagingFee, address(this)))
        );
        bridgeActions[1] =
            abi.encodeCall(IBridgeSettlerActions.BASIC, (address(token), 10000, address(this), 0, bytes("")));
        sendParam.amountLD = amount - dust;

        deal(address(this), amount + fee);
        uint256 balanceBefore = address(oft).balance;
        vm.expectCall(oft, amount + fee - dust, abi.encodeCall(IOFT.send, (sendParam, messagingFee, address(this))));
        bridgeSettler.execute{value: amount + fee}(bridgeActions, bytes32(0));
        uint256 balanceAfter = address(oft).balance;

        assertEq(balanceAfter - balanceBefore, amount - dust, "Assets were not received");
    }
}

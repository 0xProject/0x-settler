// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {BridgeSettlerIntegrationTest} from "./BridgeSettler.t.sol";
import {ALLOWANCE_HOLDER} from "src/allowanceholder/IAllowanceHolder.sol";
import {IBridgeSettlerActions} from "src/bridge/IBridgeSettlerActions.sol";
import {ArbitrumBridgeSettler} from "src/chains/Arbitrum/BridgeSettler.sol";

contract MayanProtocolDummy {
    function mayanNativeReceiver(bytes32) external payable {}

    function mayanERC20Receiver(address token, uint256 amount, bytes32) external {
        IERC20(token).transferFrom(msg.sender, address(this), amount);
    }
}

contract MayanTest is BridgeSettlerIntegrationTest {
    address forwarder = 0x337685fdaB40D39bd02028545a4FfA7D287cC3E2;
    address mayanProtocol;

    function _testBridgeSettler() internal override {
        bridgeSettler = new ArbitrumBridgeSettler(bytes20(0));
    }

    function setUp() public override {
        super.setUp();
        vm.label(forwarder, "forwarder");
        mayanProtocol = address(new MayanProtocolDummy());
        // Register mayanProtocol as a valid protocol in forwarder
        // writes to `mapping(address => bool) public mayanProtocols` at slot 3
        vm.store(address(forwarder), keccak256(abi.encode(mayanProtocol, uint256(3))), bytes32(uint256(1)));
    }

    function testBridgeNative() public {
        uint256 amount = 1000;
        bytes32 someExtraBytes = keccak256("someExtraBytesForNativeTransfer");

        deal(address(this), amount);

        bytes[] memory bridgeActions = new bytes[](1);
        bridgeActions[0] = abi.encodeCall(
            IBridgeSettlerActions.BRIDGE_NATIVE_TO_MAYAN,
            (
                forwarder,
                abi.encode(mayanProtocol, abi.encodeCall(MayanProtocolDummy.mayanNativeReceiver, (someExtraBytes)))
            )
        );

        vm.expectCall(mayanProtocol, amount, abi.encodeCall(MayanProtocolDummy.mayanNativeReceiver, (someExtraBytes)));
        bridgeSettler.execute{value: amount}(bridgeActions, bytes32(0));
        assertEq(mayanProtocol.balance, amount, "Assets were not received");
    }

    function testBridgeERC20() public {
        uint256 amount = 2000;
        bytes32 someExtraBytes = keccak256("someExtraBytesForERC20Transfer");

        deal(address(token), address(this), amount);
        token.approve(address(ALLOWANCE_HOLDER), amount);

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
        bridgeActions[1] = abi.encodeCall(
            IBridgeSettlerActions.BRIDGE_ERC20_TO_MAYAN,
            (
                forwarder,
                abi.encode(
                    mayanProtocol,
                    abi.encodeCall(MayanProtocolDummy.mayanERC20Receiver, (address(token), 0, someExtraBytes))
                )
            )
        );

        vm.expectCall(
            address(mayanProtocol),
            abi.encodeCall(MayanProtocolDummy.mayanERC20Receiver, (address(token), amount, someExtraBytes))
        );
        ALLOWANCE_HOLDER.exec(
            address(bridgeSettler),
            address(token),
            amount,
            payable(address(bridgeSettler)),
            abi.encodeCall(bridgeSettler.execute, (bridgeActions, bytes32(0)))
        );
        assertEq(token.balanceOf(mayanProtocol), amount, "Assets were not received");
    }
}

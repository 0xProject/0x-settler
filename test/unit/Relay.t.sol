// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {IBridgeSettlerActions} from "src/bridge/IBridgeSettlerActions.sol";
import {ALLOWANCE_HOLDER} from "src/allowanceholder/IAllowanceHolder.sol";
import {BridgeSettlerUnitTest} from "./BridgeSettler.t.sol";
import {Utils} from "./Utils.sol";
import {Relay} from "src/core/Relay.sol";

contract RelayTest is BridgeSettlerUnitTest, Utils {
    function testBridgeNative() public {
        address to = makeAddr("to");
        bytes32 requestId = keccak256("requestId - native transfer");

        bytes[] memory bridgeActions = new bytes[](1);
        bridgeActions[0] = abi.encodeCall(IBridgeSettlerActions.BRIDGE_NATIVE_TO_RELAY, (to, requestId));

        deal(address(this), 1000);

        vm.expectEmit(true, true, true, true);
        emit Relay.RelayAction(requestId);
        vm.expectCall(to, abi.encode(requestId));
        bridgeSettler.execute{value: 1000}(bridgeActions, bytes32(0));

        assertEq(to.balance, 1000, "Assets were not received");
    }

    function testBridgeERC20() public {
        address to = makeAddr("to");
        bytes32 requestId = keccak256("requestId - ERC20 transfer");
        uint256 amount = 1000;

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
        bridgeActions[1] = abi.encodeCall(IBridgeSettlerActions.BRIDGE_ERC20_TO_RELAY, (address(token), to, requestId));

        deal(address(token), address(this), amount);
        token.approve(address(ALLOWANCE_HOLDER), amount);

        vm.expectEmit(true, true, true, true);
        emit Relay.RelayAction(requestId);
        vm.expectCall(address(token), abi.encodePacked(abi.encodeCall(IERC20.transfer, (to, amount)), requestId));
        ALLOWANCE_HOLDER.exec(
            address(bridgeSettler),
            address(token),
            amount,
            payable(address(bridgeSettler)),
            abi.encodeCall(bridgeSettler.execute, (bridgeActions, bytes32(0)))
        );

        assertEq(token.balanceOf(to), amount, "Assets were not received");
    }
}

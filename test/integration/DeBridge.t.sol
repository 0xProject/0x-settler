// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {BridgeSettlerIntegrationTest} from "./BridgeSettler.t.sol";
import {ALLOWANCE_HOLDER} from "src/allowanceholder/IAllowanceHolder.sol";
import {IBridgeSettlerActions} from "src/bridge/IBridgeSettlerActions.sol";
import {DeBridge, DLN_SOURCE, IDlnSource} from "src/core/DeBridge.sol";

contract DeBridgeTest is BridgeSettlerIntegrationTest {
    uint256 globalFee;
    IERC20 USDC = IERC20(0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48);

    function setUp() public override {
        super.setUp();
        vm.label(address(DLN_SOURCE), "DLN_SOURCE");
        globalFee = DLN_SOURCE.globalFixedNativeFee();
    }

    function deBridgecall(address token, uint256 amount) public view returns (bytes memory) {
        return abi.encodeCall(
            IDlnSource.createSaltedOrder,
            (
                IDlnSource.OrderCreation({
                    giveTokenAddress: token,
                    giveAmount: amount,
                    takeTokenAddress: abi.encodePacked(USDC),
                    takeAmount: 1234,
                    takeChainId: 43114, // avalanche
                    receiverDst: abi.encodePacked(address(123)),
                    givePatchAuthoritySrc: address(this),
                    orderAuthorityAddressDst: abi.encodePacked(address(this)),
                    allowedTakerDst: bytes(""), // no specific taker
                    externalCall: bytes(""), // no external call
                    allowedCancelBeneficiarySrc: abi.encodePacked(address(this))
                }),
                0, // salt
                bytes(""), // no affiliateFee,
                0, // no referralCode,
                bytes(""), // no permitEnvelope,
                bytes("grafity") // metadata
            )
        );
    }

    function removeSelector(bytes memory data) public pure returns (bytes memory) {
        assembly ("memory-safe") {
            let len := sub(mload(data), 0x04)
            data := add(0x04, data)
            mstore(data, len)
        }
        return data;
    }

    function testBridgeNative() public {
        uint256 amount = 1000;

        deal(address(this), amount + globalFee);

        bytes[] memory bridgeActions = new bytes[](1);
        // amount set to zero, to make sure BridgeSettler overrides it
        bridgeActions[0] = abi.encodeCall(
            IBridgeSettlerActions.BRIDGE_TO_DEBRIDGE, (globalFee, removeSelector(deBridgecall(address(0), amount)))
        );

        uint256 balanceBefore = address(DLN_SOURCE).balance;
        vm.expectCall(address(DLN_SOURCE), amount + globalFee, deBridgecall(address(0), amount));
        bridgeSettler.execute{value: amount + globalFee}(bridgeActions, bytes32(0));
        uint256 balanceAfter = address(DLN_SOURCE).balance;

        assertEq(balanceAfter - balanceBefore, amount + globalFee, "Assets were not received");
    }

    function testBridgeERC20() public {
        uint256 amount = 2000;

        deal(address(this), globalFee);
        deal(address(USDC), address(this), amount);
        USDC.approve(address(ALLOWANCE_HOLDER), amount);

        bytes[] memory bridgeActions = new bytes[](2);
        bridgeActions[0] = abi.encodeCall(
            IBridgeSettlerActions.TRANSFER_FROM,
            (
                address(bridgeSettler),
                ISignatureTransfer.PermitTransferFrom({
                    permitted: ISignatureTransfer.TokenPermissions({token: address(USDC), amount: amount}),
                    nonce: 0,
                    deadline: block.timestamp
                }),
                bytes("")
            )
        );
        bridgeActions[1] = abi.encodeCall(
            IBridgeSettlerActions.BRIDGE_TO_DEBRIDGE, (globalFee, removeSelector(deBridgecall(address(USDC), 0)))
        );

        uint256 usdcBalanceBefore = USDC.balanceOf(address(DLN_SOURCE));
        uint256 ethBalanceBefore = address(DLN_SOURCE).balance;
        vm.expectCall(address(DLN_SOURCE), globalFee, deBridgecall(address(USDC), amount));
        ALLOWANCE_HOLDER.exec{value: globalFee}(
            address(bridgeSettler),
            address(USDC),
            amount,
            payable(address(bridgeSettler)),
            abi.encodeCall(bridgeSettler.execute, (bridgeActions, bytes32(0)))
        );
        uint256 usdcBalanceAfter = USDC.balanceOf(address(DLN_SOURCE));
        uint256 ethBalanceAfter = address(DLN_SOURCE).balance;

        assertEq(usdcBalanceAfter - usdcBalanceBefore, amount, "Assets were not received");
        assertEq(ethBalanceAfter - ethBalanceBefore, globalFee, "Fee was not received");
    }
}

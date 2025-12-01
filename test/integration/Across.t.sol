// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {BridgeSettlerIntegrationTest} from "./BridgeSettler.t.sol";
import {ALLOWANCE_HOLDER} from "src/allowanceholder/IAllowanceHolder.sol";
import {IBridgeSettlerActions} from "src/bridge/IBridgeSettlerActions.sol";

contract AcrossTest is BridgeSettlerIntegrationTest {
    address spokePool = 0x5c7BCd6E7De5423a257D81B442095A1a6ced35C5;
    IERC20 WETH = IERC20(0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2);

    function setUp() public override {
        super.setUp();
        vm.label(spokePool, "SpokePool");
    }

    function testBridgeNative() public {
        uint256 amount = 1000;

        deal(address(this), amount);

        bytes[] memory bridgeActions = new bytes[](1);
        bridgeActions[0] = abi.encodeCall(
            IBridgeSettlerActions.BRIDGE_NATIVE_TO_ACROSS,
            (
                spokePool,
                abi.encode(
                    makeAddr("depositor"),
                    makeAddr("recipient"),
                    address(WETH), // input token
                    address(0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48), // output token (USDC)
                    2000, // initial amountIn
                    4000, // initial amountOut (rate is 1:2)
                    8453, // Base chain id
                    address(0), // exclusiveRelayer
                    block.timestamp, // quoteTimestamp
                    block.timestamp + 1, // fillDeadline
                    0, // exclusivityParameter
                    "message" // message
                )
            )
        );

        uint256 balanceBefore = WETH.balanceOf(spokePool);
        vm.expectCall(
            spokePool,
            abi.encodeWithSelector(
                0xad5425c6,
                makeAddr("depositor"),
                makeAddr("recipient"),
                address(WETH), // input token
                address(0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48), // output token (USDC)
                1000, // updated amountIn
                2000, // updated amountOut (rate is 1:2)
                8453, // Base chain id
                address(0), // exclusiveRelayer
                block.timestamp, // quoteTimestamp
                block.timestamp + 1, // fillDeadline
                0, // exclusivityParameter
                "message" // message
            )
        );
        bridgeSettler.execute{value: amount}(bridgeActions, bytes32(0));
        uint256 balanceAfter = WETH.balanceOf(spokePool);

        assertEq(balanceAfter - balanceBefore, amount, "Assets were not received");
    }

    function testBridgeERC20() public {
        uint256 amount = 2000;

        deal(address(this), amount);
        (bool success,) = address(WETH).call{value: amount}(abi.encodeWithSignature("deposit()"));
        assertTrue(success, "Deposit failed");
        WETH.approve(address(ALLOWANCE_HOLDER), amount);

        bytes[] memory bridgeActions = new bytes[](2);
        bridgeActions[0] = abi.encodeCall(
            IBridgeSettlerActions.TRANSFER_FROM,
            (
                address(bridgeSettler),
                ISignatureTransfer.PermitTransferFrom({
                    permitted: ISignatureTransfer.TokenPermissions({token: address(WETH), amount: amount}),
                    nonce: 0,
                    deadline: block.timestamp
                }),
                bytes("")
            )
        );
        bridgeActions[1] = abi.encodeCall(
            IBridgeSettlerActions.BRIDGE_ERC20_TO_ACROSS,
            (
                spokePool,
                abi.encode(
                    makeAddr("depositor"),
                    makeAddr("recipient"),
                    address(WETH), // input token
                    address(0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48), // output token (USDC)
                    1000, // initial amountIn
                    1000, // initial amountOut (rate is 1:1)
                    8453, // Base chain id
                    address(0), // exclusiveRelayer
                    block.timestamp, // quoteTimestamp
                    block.timestamp + 1, // fillDeadline
                    0, // exclusivityParameter
                    "message" // message
                )
            )
        );

        uint256 balanceBefore = WETH.balanceOf(spokePool);
        vm.expectCall(
            spokePool,
            abi.encodeWithSelector(
                0xad5425c6,
                makeAddr("depositor"),
                makeAddr("recipient"),
                address(WETH), // input token
                address(0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48), // output token (USDC)
                2000, // updated amountIn
                2000, // updated amountOut
                8453, // Base chain id
                address(0), // exclusiveRelayer
                block.timestamp, // quoteTimestamp
                block.timestamp + 1, // fillDeadline
                0, // exclusivityParameter
                "message" // message
            )
        );
        ALLOWANCE_HOLDER.exec(
            address(bridgeSettler),
            address(WETH),
            amount,
            payable(address(bridgeSettler)),
            abi.encodeCall(bridgeSettler.execute, (bridgeActions, bytes32(0)))
        );
        uint256 balanceAfter = WETH.balanceOf(spokePool);

        assertEq(balanceAfter - balanceBefore, amount, "Assets were not received");
    }
}

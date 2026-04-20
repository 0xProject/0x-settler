// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {BridgeSettlerIntegrationTest} from "./BridgeSettler.t.sol";
import {ALLOWANCE_HOLDER} from "src/allowanceholder/IAllowanceHolder.sol";
import {IBridgeSettlerActions} from "src/bridge/IBridgeSettlerActions.sol";
import {LibBytes} from "../utils/LibBytes.sol";
import {ISpokePool} from "src/core/Across.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";

contract AcrossTest is BridgeSettlerIntegrationTest {
    using LibBytes for bytes;

    address spokePool = 0x5c7BCd6E7De5423a257D81B442095A1a6ced35C5;
    IERC20 WETH = IERC20(0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2);
    IERC20 USDC = IERC20(0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48);

    struct DepositParams {
        address depositor;
        address recipient;
        address inputToken;
        address outputToken;
        uint256 inputAmount;
        uint256 outputAmount;
        uint256 destinationChainId;
        address exclusiveRelayer;
        uint256 quoteTimestamp;
        uint256 fillDeadline;
        uint256 exclusivityParameter;
        bytes message;
    }

    function setUp() public override {
        super.setUp();
        vm.label(spokePool, "SpokePool");
    }

    function acrossCall(uint256 inputAmount, uint256 outputAmount) internal returns (bytes memory) {
        return abi.encodeCall(
            ISpokePool.deposit,
            (
                bytes32(uint256(uint160(makeAddr("depositor")))),
                bytes32(uint256(uint160(makeAddr("recipient")))),
                bytes32(uint256(uint160(address(WETH)))),
                bytes32(uint256(uint160(address(USDC)))),
                inputAmount,
                outputAmount,
                8453,
                bytes32(0),
                uint32(block.timestamp),
                uint32(block.timestamp + 1),
                0,
                bytes("message")
            )
        );
    }

    function testBridgeNative() public {
        uint256 amount = 1000;

        deal(address(this), amount);

        bytes[] memory bridgeActions = ActionDataBuilder.build(
            abi.encodeCall(
                IBridgeSettlerActions.BRIDGE_NATIVE_TO_ACROSS, (spokePool, acrossCall(2000, 4000).popSelector())
            )
        );

        uint256 balanceBefore = WETH.balanceOf(spokePool);
        vm.expectCall(spokePool, acrossCall(1000, 2000));
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

        bytes[] memory bridgeActions = ActionDataBuilder.build(
            _getDefaultTransferFrom(address(WETH), amount),
            abi.encodeCall(
                IBridgeSettlerActions.BRIDGE_ERC20_TO_ACROSS, (spokePool, acrossCall(1000, 1000).popSelector())
            )
        );

        uint256 balanceBefore = WETH.balanceOf(spokePool);
        vm.expectCall(spokePool, acrossCall(2000, 2000));
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

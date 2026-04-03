// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {Vm} from "@forge-std/Vm.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {BridgeSettlerIntegrationTest} from "./BridgeSettler.t.sol";
import {ALLOWANCE_HOLDER} from "src/allowanceholder/IAllowanceHolder.sol";
import {IBridgeSettlerActions} from "src/bridge/IBridgeSettlerActions.sol";
import {InvalidFeeToken, InvalidTokenAmountsLength} from "src/core/SettlerErrors.sol";
import {LibBytes} from "../utils/LibBytes.sol";
import {IRouterClient, IOnRamp} from "src/core/CCIP.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";

contract CCIPTest is BridgeSettlerIntegrationTest {
    using LibBytes for bytes;

    // CCIP Router on Ethereum Mainnet
    address constant CCIP_ROUTER = 0x80226fc0Ee2b096224EeAc085Bb9a8cba1146f7D;

    // USDC on Ethereum Mainnet - widely supported on CCIP lanes
    IERC20 constant USDC = IERC20(0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48);

    // WETH on Ethereum Mainnet - CCIP router wraps native fee payments to WETH
    IERC20 constant WETH = IERC20(0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2);

    // Chain selectors (https://docs.chain.link/cre/reference/sdk/evm-client-ts#chain-selector-reference)
    uint64 constant ARBITRUM_SELECTOR = 4949039107694359620;
    uint64 constant BASE_SELECTOR = 15971525489660198786;

    address recipient;

    receive() external payable {}

    function setUp() public override {
        super.setUp();
        vm.label(CCIP_ROUTER, "CCIPRouter");
        vm.label(address(USDC), "USDC");
        recipient = makeAddr("recipient");

        deal(address(USDC), address(this), 2000e6);
        deal(address(this), 10 ether);
        USDC.approve(address(ALLOWANCE_HOLDER), 2000e6);
    }

    function getOnRamp(uint64 destinationChainSelector) internal view returns (address onRamp) {
        // fetch the onRamp address for the destination chain
        // mapping(uint256 destChainSelector => address onRamp) private s_onRamps;
        // mapping is at slot 3
        onRamp = address(uint160(uint256(vm.load(CCIP_ROUTER, keccak256(abi.encode(destinationChainSelector, 0x3))))));
    }

    function _prepareMessage(address tokenAddress, uint256 amount)
        internal
        view
        returns (IRouterClient.EVM2AnyMessage memory message)
    {
        IRouterClient.EVMTokenAmount[] memory tokenAmounts = new IRouterClient.EVMTokenAmount[](1);
        tokenAmounts[0] = IRouterClient.EVMTokenAmount({token: tokenAddress, amount: amount});

        message = IRouterClient.EVM2AnyMessage({
            receiver: abi.encode(recipient),
            data: bytes(""),
            tokenAmounts: tokenAmounts,
            feeToken: address(0), // Pay fees in native token
            extraArgs: bytes("") // Default extra args (200k gas limit)
        });
    }

    function testBridgeUsdcToArbitrum() public {
        uint256 amount = 1000e6; // 1000 USDC (6 decimals)

        // Prepare the CCIP message
        IRouterClient.EVM2AnyMessage memory message = _prepareMessage(address(USDC), amount);

        // Get the fee for the transfer
        uint256 fee = IRouterClient(CCIP_ROUTER).getFee(ARBITRUM_SELECTOR, message);

        // Snapshot balances before execution
        address onRamp = getOnRamp(ARBITRUM_SELECTOR);
        uint256 onRampWethBefore = WETH.balanceOf(onRamp);
        uint256 usdcSupplyBefore = USDC.totalSupply();
        uint256 usdcBalanceBefore = USDC.balanceOf(address(this));

        // Set amount to 0 in message - the action will inject the actual balance
        message.tokenAmounts[0].amount = 0;
        // Build bridge actions
        bytes[] memory bridgeActions = ActionDataBuilder.build(
            _getDefaultTransferFrom(address(USDC), amount),
            abi.encodeCall(
                IBridgeSettlerActions.BRIDGE_TO_CCIP,
                (CCIP_ROUTER, abi.encodeCall(IRouterClient.ccipSend, (ARBITRUM_SELECTOR, message)).popSelector())
            )
        );
        // Restore amount for expectCall
        message.tokenAmounts[0].amount = amount;

        // Execute and verify
        vm.expectCall(CCIP_ROUTER, fee, abi.encodeCall(IRouterClient.ccipSend, (ARBITRUM_SELECTOR, message)));
        ALLOWANCE_HOLDER.exec{value: fee}(
            address(bridgeSettler),
            address(USDC),
            amount,
            payable(address(bridgeSettler)),
            abi.encodeCall(bridgeSettler.execute, (bridgeActions, bytes32(0)))
        );

        // Verify USDC was transferred from us
        assertEq(USDC.balanceOf(address(this)), usdcBalanceBefore - amount, "USDC balance should have decreased");
        // Verify the onRamp received the fee in WETH
        assertEq(WETH.balanceOf(onRamp), onRampWethBefore + fee, "onRamp should have received the fee in WETH");
        // Verify USDC was burned (supply decreased)
        assertEq(USDC.totalSupply(), usdcSupplyBefore - amount, "USDC supply should have decreased by bridged amount");
    }

    function testBridgeUsdcToBase() public {
        uint256 amount = 500e6; // 500 USDC (6 decimals)

        // Prepare the CCIP message
        IRouterClient.EVM2AnyMessage memory message = _prepareMessage(address(USDC), amount);

        // Get the fee for the transfer
        uint256 fee = IRouterClient(CCIP_ROUTER).getFee(BASE_SELECTOR, message);

        // Snapshot balances before execution
        address onRamp = getOnRamp(BASE_SELECTOR);
        uint256 onRampWethBefore = WETH.balanceOf(onRamp);
        uint256 usdcSupplyBefore = USDC.totalSupply();
        uint256 usdcBalanceBefore = USDC.balanceOf(address(this));

        // Set amount to 0 in message - the action will inject the actual balance
        message.tokenAmounts[0].amount = 0;
        // Build bridge actions
        bytes[] memory bridgeActions = ActionDataBuilder.build(
            _getDefaultTransferFrom(address(USDC), amount),
            abi.encodeCall(
                IBridgeSettlerActions.BRIDGE_TO_CCIP,
                (CCIP_ROUTER, abi.encodeCall(IRouterClient.ccipSend, (BASE_SELECTOR, message)).popSelector())
            )
        );
        // Restore amount for expectCall
        message.tokenAmounts[0].amount = amount;

        // Execute
        vm.expectCall(CCIP_ROUTER, fee, abi.encodeCall(IRouterClient.ccipSend, (BASE_SELECTOR, message)));
        ALLOWANCE_HOLDER.exec{value: fee}(
            address(bridgeSettler),
            address(USDC),
            amount,
            payable(address(bridgeSettler)),
            abi.encodeCall(bridgeSettler.execute, (bridgeActions, bytes32(0)))
        );

        assertEq(USDC.balanceOf(address(this)), usdcBalanceBefore - amount, "USDC balance should have decreased");
        // Verify the onRamp received the fee in WETH
        assertEq(WETH.balanceOf(onRamp), onRampWethBefore + fee, "onRamp should have received the fee in WETH");
        // Verify USDC was burned (supply decreased)
        assertEq(USDC.totalSupply(), usdcSupplyBefore - amount, "USDC supply should have decreased by bridged amount");
    }

    function testBridgeWithData() public {
        uint256 amount = 100e6; // 100 USDC (6 decimals)
        bytes memory crossChainData = abi.encode("Hello CCIP!");

        // Prepare the CCIP message with data payload
        IRouterClient.EVMTokenAmount[] memory tokenAmounts = new IRouterClient.EVMTokenAmount[](1);
        tokenAmounts[0] = IRouterClient.EVMTokenAmount({token: address(USDC), amount: amount});

        IRouterClient.EVM2AnyMessage memory message = IRouterClient.EVM2AnyMessage({
            receiver: abi.encode(recipient),
            data: crossChainData,
            tokenAmounts: tokenAmounts,
            feeToken: address(0),
            extraArgs: bytes("")
        });

        // Get the fee
        uint256 fee = IRouterClient(CCIP_ROUTER).getFee(ARBITRUM_SELECTOR, message);

        // Snapshot balances before execution
        address onRamp = getOnRamp(ARBITRUM_SELECTOR);
        uint256 onRampWethBefore = WETH.balanceOf(onRamp);
        uint256 usdcSupplyBefore = USDC.totalSupply();
        uint256 usdcBalanceBefore = USDC.balanceOf(address(this));

        // Set amount to 0 in message - the action will inject the actual balance
        message.tokenAmounts[0].amount = 0;
        // Build bridge actions
        bytes[] memory bridgeActions = ActionDataBuilder.build(
            _getDefaultTransferFrom(address(USDC), amount),
            abi.encodeCall(
                IBridgeSettlerActions.BRIDGE_TO_CCIP,
                (CCIP_ROUTER, abi.encodeCall(IRouterClient.ccipSend, (ARBITRUM_SELECTOR, message)).popSelector())
            )
        );
        // Restore amount for expectCall
        message.tokenAmounts[0].amount = amount;

        // Execute
        vm.expectCall(CCIP_ROUTER, fee, abi.encodeCall(IRouterClient.ccipSend, (ARBITRUM_SELECTOR, message)));
        vm.recordLogs();
        ALLOWANCE_HOLDER.exec{value: fee}(
            address(bridgeSettler),
            address(USDC),
            amount,
            payable(address(bridgeSettler)),
            abi.encodeCall(bridgeSettler.execute, (bridgeActions, bytes32(0)))
        );

        assertEq(USDC.balanceOf(address(this)), usdcBalanceBefore - amount, "USDC balance should have decreased");
        assertEq(WETH.balanceOf(onRamp), onRampWethBefore + fee, "onRamp should have received the fee in WETH");
        assertEq(USDC.totalSupply(), usdcSupplyBefore - amount, "USDC supply should have decreased by bridged amount");

        // Verify CCIPSendRequested was emitted from onRamp and contains our crossChainData
        // event CCIPSendRequested(IOnRamp.EVM2EVMMessage message)
        bytes32 ccipTopic = 0xd0c3c799bf9e2639de44391e7f524d229b2b55f5b1ea94b2bf7da42f7243dddd;
        Vm.Log[] memory logs = vm.getRecordedLogs();
        uint256 ccipSendRequestedCount = 0;
        for (uint256 i = 0; i < logs.length; i++) {
            if (logs[i].topics[0] == ccipTopic && logs[i].emitter == onRamp) {
                IOnRamp.EVM2EVMMessage memory ccipMsg = abi.decode(logs[i].data, (IOnRamp.EVM2EVMMessage));
                assertEq(ccipMsg.data, crossChainData, "CCIPSendRequested data should match crossChainData");
                ccipSendRequestedCount++;
            }
        }
        assertEq(ccipSendRequestedCount, 1, "CCIPSendRequested event not emitted");
    }

    function testRevertIfFeeTokenNotZero() public {
        uint256 amount = 1000e6;

        // Prepare a CCIP message with non-zero feeToken (USDC as fee token)
        IRouterClient.EVMTokenAmount[] memory tokenAmounts = new IRouterClient.EVMTokenAmount[](1);
        tokenAmounts[0] = IRouterClient.EVMTokenAmount({token: address(USDC), amount: amount});

        IRouterClient.EVM2AnyMessage memory message = IRouterClient.EVM2AnyMessage({
            receiver: abi.encode(recipient),
            data: bytes(""),
            tokenAmounts: tokenAmounts,
            feeToken: address(USDC), // Non-zero feeToken should cause revert
            extraArgs: bytes("")
        });

        // Set amount to 0 in message - the action will inject the actual balance
        message.tokenAmounts[0].amount = 0;
        // Build bridge actions
        bytes[] memory bridgeActions = ActionDataBuilder.build(
            _getDefaultTransferFrom(address(USDC), amount),
            abi.encodeCall(
                IBridgeSettlerActions.BRIDGE_TO_CCIP,
                (CCIP_ROUTER, abi.encodeCall(IRouterClient.ccipSend, (ARBITRUM_SELECTOR, message)).popSelector())
            )
        );
        // Restore amount for expectCall
        message.tokenAmounts[0].amount = amount;

        // Should revert because feeToken is not address(0)
        vm.expectRevert(InvalidFeeToken.selector);
        ALLOWANCE_HOLDER.exec(
            address(bridgeSettler),
            address(USDC),
            amount,
            payable(address(bridgeSettler)),
            abi.encodeCall(bridgeSettler.execute, (bridgeActions, bytes32(0)))
        );
    }

    function testRevertIfTokenAmountsLengthNotOne() public {
        uint256 amount = 1000e6;

        // Prepare a CCIP message with 2 tokenAmounts elements
        IRouterClient.EVMTokenAmount[] memory tokenAmounts = new IRouterClient.EVMTokenAmount[](2);
        tokenAmounts[0] = IRouterClient.EVMTokenAmount({token: address(USDC), amount: amount});
        tokenAmounts[1] = IRouterClient.EVMTokenAmount({token: address(USDC), amount: amount});

        IRouterClient.EVM2AnyMessage memory message = IRouterClient.EVM2AnyMessage({
            receiver: abi.encode(recipient),
            data: bytes(""),
            tokenAmounts: tokenAmounts,
            feeToken: address(0),
            extraArgs: bytes("")
        });

        // Set amount to 0 in message - the action will inject the actual balance
        message.tokenAmounts[0].amount = 0;
        // Build bridge actions
        bytes[] memory bridgeActions = ActionDataBuilder.build(
            _getDefaultTransferFrom(address(USDC), amount),
            abi.encodeCall(
                IBridgeSettlerActions.BRIDGE_TO_CCIP,
                (CCIP_ROUTER, abi.encodeCall(IRouterClient.ccipSend, (ARBITRUM_SELECTOR, message)).popSelector())
            )
        );
        // Restore amount for expectCall
        message.tokenAmounts[0].amount = amount;

        // Should revert because tokenAmounts length is not 1
        vm.expectRevert(InvalidTokenAmountsLength.selector);
        ALLOWANCE_HOLDER.exec(
            address(bridgeSettler),
            address(USDC),
            amount,
            payable(address(bridgeSettler)),
            abi.encodeCall(bridgeSettler.execute, (bridgeActions, bytes32(0)))
        );
    }
}

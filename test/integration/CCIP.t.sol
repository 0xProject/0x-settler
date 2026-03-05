// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {BridgeSettlerIntegrationTest} from "./BridgeSettler.t.sol";
import {ALLOWANCE_HOLDER} from "src/allowanceholder/IAllowanceHolder.sol";
import {IBridgeSettlerActions} from "src/bridge/IBridgeSettlerActions.sol";

/// @dev Interface for CCIP Router
interface IRouterClient {
    struct EVMTokenAmount {
        address token;
        uint256 amount;
    }

    struct EVM2AnyMessage {
        bytes receiver;
        bytes data;
        EVMTokenAmount[] tokenAmounts;
        address feeToken;
        bytes extraArgs;
    }

    function ccipSend(uint64 destinationChainSelector, EVM2AnyMessage calldata message)
        external
        payable
        returns (bytes32);

    function getFee(uint64 destinationChainSelector, EVM2AnyMessage calldata message)
        external
        view
        returns (uint256);

    function isChainSupported(uint64 chainSelector) external view returns (bool);
}

contract CCIPTest is BridgeSettlerIntegrationTest {
    // CCIP Router on Ethereum Mainnet
    address constant CCIP_ROUTER = 0x80226fc0Ee2b096224EeAc085Bb9a8cba1146f7D;

    // WETH on Ethereum Mainnet
    IERC20 constant WETH = IERC20(0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2);

    // Chain selectors
    uint64 constant ARBITRUM_SELECTOR = 4949039107694359620;
    uint64 constant BASE_SELECTOR = 15971525489660198786;

    receive() external payable {}

    function setUp() public override {
        super.setUp();
        vm.label(CCIP_ROUTER, "CCIPRouter");
        vm.label(address(WETH), "WETH");
    }

    function _prepareMessage(address tokenAddress, uint256 amount, address recipient)
        internal
        pure
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

    function testBridgeWethToArbitrum() public {
        uint256 amount = 1 ether;
        address recipient = makeAddr("recipient");

        // Prepare the CCIP message
        IRouterClient.EVM2AnyMessage memory message = _prepareMessage(address(WETH), amount, recipient);

        // Get the fee for the transfer
        uint256 fee = IRouterClient(CCIP_ROUTER).getFee(ARBITRUM_SELECTOR, message);

        // Fund the test contract with WETH
        deal(address(this), amount);
        (bool success,) = address(WETH).call{value: amount}(abi.encodeWithSignature("deposit()"));
        assertTrue(success, "WETH deposit failed");
        deal(address(this), fee);
        WETH.approve(address(ALLOWANCE_HOLDER), amount);

        // Build bridge actions
        bytes[] memory bridgeActions = new bytes[](2);

        // Action 1: Transfer WETH to BridgeSettler
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

        // Action 2: Bridge via CCIP
        // Set amount to 0 in message - the action will inject the actual balance
        message.tokenAmounts[0].amount = 0;
        bytes memory ccipSendData = abi.encode(ARBITRUM_SELECTOR, message);
        bridgeActions[1] =
            abi.encodeCall(IBridgeSettlerActions.BRIDGE_TO_CCIP, (address(WETH), CCIP_ROUTER, ccipSendData));

        // Restore amount for expectCall
        message.tokenAmounts[0].amount = amount;

        // Execute and verify
        vm.expectCall(CCIP_ROUTER, fee, abi.encodeCall(IRouterClient.ccipSend, (ARBITRUM_SELECTOR, message)));
        ALLOWANCE_HOLDER.exec{value: fee}(
            address(bridgeSettler),
            address(WETH),
            amount,
            payable(address(bridgeSettler)),
            abi.encodeCall(bridgeSettler.execute, (bridgeActions, bytes32(0)))
        );

        // Verify our balance is gone
        assertEq(WETH.balanceOf(address(this)), 0, "WETH should have been transferred");
    }

    function testBridgeWethToBase() public {
        uint256 amount = 0.5 ether;
        address recipient = makeAddr("recipient");

        // Prepare the CCIP message
        IRouterClient.EVM2AnyMessage memory message = _prepareMessage(address(WETH), amount, recipient);

        // Get the fee for the transfer
        uint256 fee = IRouterClient(CCIP_ROUTER).getFee(BASE_SELECTOR, message);

        // Fund the test contract with WETH
        deal(address(this), amount);
        (bool success,) = address(WETH).call{value: amount}(abi.encodeWithSignature("deposit()"));
        assertTrue(success, "WETH deposit failed");
        deal(address(this), fee);
        WETH.approve(address(ALLOWANCE_HOLDER), amount);

        // Build bridge actions
        bytes[] memory bridgeActions = new bytes[](2);

        // Action 1: Transfer WETH to BridgeSettler
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

        // Action 2: Bridge via CCIP
        message.tokenAmounts[0].amount = 0;
        bytes memory ccipSendData = abi.encode(BASE_SELECTOR, message);
        bridgeActions[1] =
            abi.encodeCall(IBridgeSettlerActions.BRIDGE_TO_CCIP, (address(WETH), CCIP_ROUTER, ccipSendData));

        // Restore amount for expectCall
        message.tokenAmounts[0].amount = amount;

        // Execute
        vm.expectCall(CCIP_ROUTER, fee, abi.encodeCall(IRouterClient.ccipSend, (BASE_SELECTOR, message)));
        ALLOWANCE_HOLDER.exec{value: fee}(
            address(bridgeSettler),
            address(WETH),
            amount,
            payable(address(bridgeSettler)),
            abi.encodeCall(bridgeSettler.execute, (bridgeActions, bytes32(0)))
        );

        assertEq(WETH.balanceOf(address(this)), 0, "WETH should have been transferred");
    }

    function testBridgeWithData() public {
        uint256 amount = 0.1 ether;
        address recipient = makeAddr("recipient");
        bytes memory crossChainData = abi.encode("Hello CCIP!");

        // Prepare the CCIP message with data payload
        IRouterClient.EVMTokenAmount[] memory tokenAmounts = new IRouterClient.EVMTokenAmount[](1);
        tokenAmounts[0] = IRouterClient.EVMTokenAmount({token: address(WETH), amount: amount});

        IRouterClient.EVM2AnyMessage memory message = IRouterClient.EVM2AnyMessage({
            receiver: abi.encode(recipient),
            data: crossChainData,
            tokenAmounts: tokenAmounts,
            feeToken: address(0),
            extraArgs: bytes("")
        });

        // Get the fee
        uint256 fee = IRouterClient(CCIP_ROUTER).getFee(ARBITRUM_SELECTOR, message);

        // Fund with WETH
        deal(address(this), amount);
        (bool success,) = address(WETH).call{value: amount}(abi.encodeWithSignature("deposit()"));
        assertTrue(success, "WETH deposit failed");
        deal(address(this), fee);
        WETH.approve(address(ALLOWANCE_HOLDER), amount);

        // Build actions
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

        message.tokenAmounts[0].amount = 0;
        bytes memory ccipSendData = abi.encode(ARBITRUM_SELECTOR, message);
        bridgeActions[1] =
            abi.encodeCall(IBridgeSettlerActions.BRIDGE_TO_CCIP, (address(WETH), CCIP_ROUTER, ccipSendData));

        message.tokenAmounts[0].amount = amount;

        // Execute
        vm.expectCall(CCIP_ROUTER, fee, abi.encodeCall(IRouterClient.ccipSend, (ARBITRUM_SELECTOR, message)));
        ALLOWANCE_HOLDER.exec{value: fee}(
            address(bridgeSettler),
            address(WETH),
            amount,
            payable(address(bridgeSettler)),
            abi.encodeCall(bridgeSettler.execute, (bridgeActions, bytes32(0)))
        );

        assertEq(WETH.balanceOf(address(this)), 0, "WETH should have been transferred");
    }
}

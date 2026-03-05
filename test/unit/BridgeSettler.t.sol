// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "@forge-std/Test.sol";
import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ALLOWANCE_HOLDER} from "src/allowanceholder/IAllowanceHolder.sol";
import {BridgeSettler, BridgeSettlerBase} from "src/bridge/BridgeSettler.sol";
import {ISettlerTakerSubmitted} from "src/interfaces/ISettlerTakerSubmitted.sol";
import {MainnetSettler} from "src/chains/Mainnet/TakerSubmitted.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {IBridgeSettlerActions} from "src/bridge/IBridgeSettlerActions.sol";
import {DAI, USDC} from "src/core/MakerPSM.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {Utils} from "./Utils.sol";
import {DEPLOYER} from "src/deployer/DeployerAddress.sol";
import {IERC721View} from "src/deployer/IDeployer.sol";
import {MockERC20} from "@solmate/test/utils/mocks/MockERC20.sol";

contract BridgeSettlerDummy is BridgeSettler {
    constructor(bytes20 gitCommit) BridgeSettlerBase(gitCommit) {}
}

contract BridgeDummy {
    function take(address token, uint256 amount) external {
        IERC20(token).transferFrom(msg.sender, address(this), amount);
    }

    receive() external payable {}
}

/// @dev Mock CCIP Router for testing
contract MockCCIPRouter {
    uint256 public lastDestinationChainSelector;
    address public lastTokenReceived;
    uint256 public lastTokenAmount;
    uint256 public lastNativeFeeReceived;
    bytes public lastReceiver;
    bytes public lastData;
    address public lastFeeToken;

    /// @dev ccipSend(uint64,(bytes,bytes,(address,uint256)[],address,bytes))
    /// selector: 0x96f4e9f9
    function ccipSend(uint64 destinationChainSelector, EVM2AnyMessage calldata message)
        external
        payable
        returns (bytes32)
    {
        lastDestinationChainSelector = destinationChainSelector;
        lastReceiver = message.receiver;
        lastData = message.data;
        lastFeeToken = message.feeToken;
        lastNativeFeeReceived = msg.value;

        if (message.tokenAmounts.length > 0) {
            lastTokenReceived = message.tokenAmounts[0].token;
            lastTokenAmount = message.tokenAmounts[0].amount;
            // Transfer tokens from sender
            IERC20(message.tokenAmounts[0].token).transferFrom(
                msg.sender, address(this), message.tokenAmounts[0].amount
            );
        }

        return keccak256(abi.encode(destinationChainSelector, message));
    }

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
}

contract BridgeSettlerTestBase is Test {
    BridgeSettler bridgeSettler;
    ISettlerTakerSubmitted settler;
    IERC20 token;
    BridgeDummy bridgeDummy;

    function _testBridgeSettler() internal virtual {
        bridgeSettler = new BridgeSettlerDummy(bytes20(0));
    }

    function setUp() public virtual {
        _testBridgeSettler();
        vm.label(address(bridgeSettler), "BridgeSettler");
        bridgeDummy = new BridgeDummy();
        token = IERC20(address(new MockERC20("Test Token", "TT", 18)));
    }
}

contract BridgeSettlerUnitTest is BridgeSettlerTestBase {
    function setUp() public override {
        super.setUp();

        vm.etch(address(ALLOWANCE_HOLDER), vm.getDeployedCode("AllowanceHolder.sol:AllowanceHolder"));
        // Mock DAI and USDC for MainnetSettler to be usable
        deployCodeTo("MockERC20", abi.encode("DAI", "DAI", 18), address(DAI));
        deployCodeTo("MockERC20", abi.encode("USDC", "USDC", 6), address(USDC));
        settler = new MainnetSettler(bytes20(0));
    }
}

contract BridgeSettlerTest is BridgeSettlerUnitTest, Utils {
    function testUserFlow() public {
        address user = makeAddr("user");
        uint256 amount = 2000;

        bytes[] memory settlerActions = new bytes[](2);
        // Take the assets from BridgeSettler
        settlerActions[0] = abi.encodeCall(
            ISettlerActions.TRANSFER_FROM,
            (
                address(settler),
                ISignatureTransfer.PermitTransferFrom({
                    permitted: ISignatureTransfer.TokenPermissions({token: address(token), amount: amount}),
                    nonce: 0,
                    deadline: block.timestamp
                }),
                bytes("")
            )
        );
        // Just send them back to BridgeSettler
        settlerActions[1] = abi.encodeCall(
            ISettlerActions.BASIC,
            (address(token), 10_000, address(token), 0x24, abi.encodeCall(IERC20.transfer, (address(bridgeSettler), 0)))
        );

        bytes[] memory bridgeActions = new bytes[](3);
        // Take the assets from the BridgeSettler
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
        // Do a swap (that just takes and returns the assets)
        bridgeActions[1] = abi.encodeCall(
            IBridgeSettlerActions.SETTLER_SWAP,
            (
                address(token),
                amount,
                address(settler),
                abi.encodeCall(
                    ISettlerTakerSubmitted.execute,
                    (
                        ISettlerBase.AllowedSlippage({
                            recipient: payable(address(0)),
                            buyToken: IERC20(address(0)),
                            minAmountOut: 0
                        }),
                        settlerActions,
                        bytes32(0)
                    )
                )
            )
        );
        // Bridge the assets to the dummy bridge
        bridgeActions[2] = abi.encodeCall(
            IBridgeSettlerActions.BASIC,
            (address(token), 10_000, address(bridgeDummy), 0x24, abi.encodeCall(BridgeDummy.take, (address(token), 0)))
        );

        vm.prank(user);
        token.approve(address(ALLOWANCE_HOLDER), type(uint256).max);
        deal(address(token), user, amount);

        _mockExpectCall(address(DEPLOYER), abi.encodeCall(IERC721View.ownerOf, (2)), abi.encode(address(settler)));
        vm.prank(user);
        ALLOWANCE_HOLDER.exec(
            address(bridgeSettler),
            address(token),
            amount,
            payable(address(bridgeSettler)),
            abi.encodeCall(BridgeSettler.execute, (bridgeActions, bytes32(0)))
        );

        assertEq(token.balanceOf(address(bridgeDummy)), amount, "Bridge did not receive the assets");
    }

    function testUserFlowWithNative() public {
        address user = makeAddr("user");
        address ETH_ADDRESS = address(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE);
        uint256 amount = 1000;

        bytes[] memory settlerActions = new bytes[](1);
        // Just send Native back to BridgeSettler
        settlerActions[0] =
            abi.encodeCall(ISettlerActions.BASIC, (ETH_ADDRESS, 10_000, address(bridgeSettler), 0x00, bytes("")));

        bytes[] memory bridgeActions = new bytes[](2);
        // Do a swap (that just sends and return the assets)
        bridgeActions[0] = abi.encodeCall(
            IBridgeSettlerActions.SETTLER_SWAP,
            (
                ETH_ADDRESS,
                amount,
                address(settler),
                abi.encodeCall(
                    ISettlerTakerSubmitted.execute,
                    (
                        ISettlerBase.AllowedSlippage({
                            recipient: payable(address(0)),
                            buyToken: IERC20(address(0)),
                            minAmountOut: 0
                        }),
                        settlerActions,
                        bytes32(0)
                    )
                )
            )
        );
        // Bridge the assets to the dummy bridge
        bridgeActions[1] =
            abi.encodeCall(IBridgeSettlerActions.BASIC, (ETH_ADDRESS, 10_000, address(bridgeDummy), 0, bytes("")));

        deal(user, amount);

        _mockExpectCall(address(DEPLOYER), abi.encodeCall(IERC721View.ownerOf, (2)), abi.encode(address(settler)));
        vm.prank(user);
        bridgeSettler.execute{value: amount}(bridgeActions, bytes32(0));

        assertEq(address(bridgeDummy).balance, amount, "Bridge did not receive the assets");
    }

    function testBridgeToCCIP() public {
        address user = makeAddr("user");
        uint256 tokenAmount = 1000e18;
        uint256 nativeFee = 0.1 ether;
        uint64 destinationChainSelector = 5009297550715157269; // Example: Arbitrum chain selector

        MockCCIPRouter ccipRouter = new MockCCIPRouter();

        // Build the EVM2AnyMessage struct
        MockCCIPRouter.EVMTokenAmount[] memory tokenAmounts = new MockCCIPRouter.EVMTokenAmount[](1);
        tokenAmounts[0] = MockCCIPRouter.EVMTokenAmount({
            token: address(token),
            amount: 0 // Will be overwritten by the action
        });

        MockCCIPRouter.EVM2AnyMessage memory message = MockCCIPRouter.EVM2AnyMessage({
            receiver: abi.encode(user), // Destination receiver
            data: bytes(""), // No data payload
            tokenAmounts: tokenAmounts,
            feeToken: address(0), // Native token for fees
            extraArgs: bytes("") // Default extra args
        });

        // Encode ccipSend arguments (without selector)
        bytes memory ccipSendData = abi.encode(destinationChainSelector, message);

        bytes[] memory bridgeActions = new bytes[](1);
        bridgeActions[0] = abi.encodeCall(
            IBridgeSettlerActions.BRIDGE_TO_CCIP, (address(token), address(ccipRouter), ccipSendData)
        );

        // Fund the BridgeSettler with tokens and native
        deal(address(token), address(bridgeSettler), tokenAmount);
        deal(address(bridgeSettler), nativeFee);

        // Execute the bridge action
        vm.prank(user);
        bridgeSettler.execute(bridgeActions, bytes32(0));

        // Verify the CCIP router received the correct values
        assertEq(ccipRouter.lastDestinationChainSelector(), destinationChainSelector, "Wrong destination chain");
        assertEq(ccipRouter.lastTokenReceived(), address(token), "Wrong token");
        assertEq(ccipRouter.lastTokenAmount(), tokenAmount, "Wrong token amount");
        assertEq(ccipRouter.lastNativeFeeReceived(), nativeFee, "Wrong native fee");
        assertEq(ccipRouter.lastFeeToken(), address(0), "Fee token should be address(0)");
        assertEq(token.balanceOf(address(ccipRouter)), tokenAmount, "Router did not receive tokens");
    }

    function testBridgeToCCIPWithData() public {
        address user = makeAddr("user");
        uint256 tokenAmount = 500e18;
        uint256 nativeFee = 0.05 ether;
        uint64 destinationChainSelector = 4949039107694359620; // Example: Base chain selector
        bytes memory crossChainData = abi.encode("Hello CCIP!");

        MockCCIPRouter ccipRouter = new MockCCIPRouter();

        // Build the EVM2AnyMessage struct with data payload
        MockCCIPRouter.EVMTokenAmount[] memory tokenAmounts = new MockCCIPRouter.EVMTokenAmount[](1);
        tokenAmounts[0] = MockCCIPRouter.EVMTokenAmount({
            token: address(token),
            amount: 0 // Will be overwritten
        });

        MockCCIPRouter.EVM2AnyMessage memory message = MockCCIPRouter.EVM2AnyMessage({
            receiver: abi.encode(makeAddr("receiver")),
            data: crossChainData,
            tokenAmounts: tokenAmounts,
            feeToken: address(0),
            extraArgs: abi.encode(uint256(200000)) // Gas limit
        });

        bytes memory ccipSendData = abi.encode(destinationChainSelector, message);

        bytes[] memory bridgeActions = new bytes[](1);
        bridgeActions[0] = abi.encodeCall(
            IBridgeSettlerActions.BRIDGE_TO_CCIP, (address(token), address(ccipRouter), ccipSendData)
        );

        deal(address(token), address(bridgeSettler), tokenAmount);
        deal(address(bridgeSettler), nativeFee);

        vm.prank(user);
        bridgeSettler.execute(bridgeActions, bytes32(0));

        assertEq(ccipRouter.lastTokenAmount(), tokenAmount, "Wrong token amount");
        assertEq(ccipRouter.lastNativeFeeReceived(), nativeFee, "Wrong native fee");
        assertEq(keccak256(ccipRouter.lastData()), keccak256(crossChainData), "Wrong data payload");
    }
}

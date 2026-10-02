// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {MockERC20} from "@solmate/test/utils/mocks/MockERC20.sol";
import {ALLOWANCE_HOLDER} from "src/allowanceholder/IAllowanceHolder.sol";
import {BridgeSettlerBase} from "src/bridge/BridgeSettlerBase.sol";
import {IBridgeSettlerActions} from "src/bridge/IBridgeSettlerActions.sol";
import {BridgeSettlerTestBase, BridgeDummy} from "../BridgeSettler.t.sol";
import {ActionDataBuilder} from "../../utils/ActionDataBuilder.sol";
import {LibBytes} from "../../utils/LibBytes.sol";
import {SettlerAbstract} from "src/SettlerAbstract.sol";
import {MainnetBridgeSettler} from "src/chains/Mainnet/BridgeSettler.sol";
import {TempoBridgeSettler} from "src/chains/Tempo/BridgeSettler.sol";
import {ISpokePool} from "src/core/Across.sol";
import {IRouterClient, IOnRamp} from "src/core/CCIP.sol";
import {IDlnSource, DLN_SOURCE} from "src/core/DeBridge.sol";
import {IOFT} from "src/core/LayerZeroOFT.sol";
import {MAYAN_FORWARDER} from "src/core/Mayan.sol";
import {INucleusTeller} from "src/core/NucleusTeller.sol";
import {ReceivePolicyBlocked} from "src/core/SettlerErrors.sol";

contract BridgeRecipientCheckHarness is MainnetBridgeSettler {
    address private immutable expectedRecipient;
    IERC20 private immutable expectedToken;

    constructor(address recipient, IERC20 token) MainnetBridgeSettler(bytes20(0)) {
        expectedRecipient = recipient;
        expectedToken = token;
    }

    function _hasRecipientCheck() internal pure override(SettlerAbstract, BridgeSettlerBase) returns (bool) {
        return true;
    }

    function _checkRecipient(address recipient, IERC20 token)
        internal
        view
        override(SettlerAbstract, BridgeSettlerBase)
    {
        require(recipient == expectedRecipient && token == expectedToken);
        revert ReceivePolicyBlocked(recipient);
    }
}

contract TempoBridgeRecipientCheckHarness is TempoBridgeSettler {
    constructor() TempoBridgeSettler(bytes20(0)) {}

    function hasRecipientCheck() external pure returns (bool) {
        return _hasRecipientCheck();
    }
}

contract BridgeRecipientCheckUnitTest is BridgeSettlerTestBase {
    using LibBytes for bytes;

    address private recipient;

    function setUp() public override {
        super.setUp();
        recipient = makeAddr("recipient");
    }

    function test_RecipientCheck_TransferFrom_Reverts() public {
        _expectBlocked(_getDefaultTransferFrom(recipient, address(token), 1 ether), recipient);
    }

    function test_RecipientCheck_Relay_Reverts() public {
        _expectBlocked(
            abi.encodeCall(IBridgeSettlerActions.BRIDGE_ERC20_TO_RELAY, (address(token), recipient, bytes32(0))),
            recipient
        );
    }

    function test_RecipientCheck_Relay_ZeroBalance_Reverts() public {
        BridgeRecipientCheckHarness checkedSettler = new BridgeRecipientCheckHarness(recipient, token);
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(IBridgeSettlerActions.BRIDGE_ERC20_TO_RELAY, (address(token), recipient, bytes32(0)))
        );
        vm.expectRevert(abi.encodeWithSelector(ReceivePolicyBlocked.selector, recipient));
        checkedSettler.execute(actions, bytes32(0));
    }

    function test_RecipientCheck_Across_DepositPool_Reverts() public {
        bytes memory data = abi.encodeCall(
                ISpokePool.deposit,
                (
                    bytes32(uint256(uint160(address(this)))),
                    bytes32(uint256(uint160(makeAddr("destination recipient")))),
                    bytes32(uint256(uint160(address(token)))),
                    bytes32(0),
                    1 ether,
                    1 ether,
                    1,
                    bytes32(0),
                    0,
                    0,
                    0,
                    ""
                )
            ).popSelector();
        _expectBlocked(abi.encodeCall(IBridgeSettlerActions.BRIDGE_ERC20_TO_ACROSS, (recipient, data)), recipient);
    }

    function test_RecipientCheck_LayerZeroOFT_Adapter_Reverts() public {
        _expectBlocked(
            abi.encodeCall(IBridgeSettlerActions.BRIDGE_TO_LAYER_ZERO_OFT, (address(token), recipient, _oftData())),
            recipient
        );
    }

    function test_RecipientCheck_StargateV2_Pool_Reverts() public {
        _expectBlocked(
            abi.encodeCall(IBridgeSettlerActions.BRIDGE_TO_STARGATE_V2, (address(token), recipient, _oftData())),
            recipient
        );
    }

    function test_RecipientCheck_DeBridge_Source_Reverts() public {
        IDlnSource.OrderCreation memory order;
        order.giveTokenAddress = address(token);
        bytes memory data = abi.encodeCall(IDlnSource.createSaltedOrder, (order, 0, "", 0, "", "")).popSelector();
        _expectBlocked(abi.encodeCall(IBridgeSettlerActions.BRIDGE_TO_DEBRIDGE, (0, data)), address(DLN_SOURCE));
    }

    function test_RecipientCheck_Mayan_Forwarder_Reverts() public {
        bytes memory data = abi.encode(recipient, abi.encodeCall(BridgeDummy.take, (address(token), 0)));
        _expectBlocked(abi.encodeCall(IBridgeSettlerActions.BRIDGE_ERC20_TO_MAYAN, (data)), address(MAYAN_FORWARDER));
    }

    function test_RecipientCheck_NucleusTeller_Vault_Reverts() public {
        INucleusTeller.BridgeData memory bridgeData;
        bytes memory data = abi.encodeCall(INucleusTeller.depositAndBridge, (token, 0, 0, bridgeData)).popSelector();
        _expectBlocked(
            abi.encodeCall(IBridgeSettlerActions.DEPOSIT_AND_BRIDGE_TO_NUCLEUS_TELLER, (data)),
            0x5cB5C4d5e8B184A364534bc688DA0553Ccf8F484
        );
    }

    function test_RecipientCheck_CCIP_TokenPool_Reverts() public {
        address onRamp = makeAddr("onRamp");
        uint64 destinationChainSelector = type(uint64).max;
        vm.mockCall(
            address(bridgeDummy),
            abi.encodeCall(IRouterClient.getOnRamp, (destinationChainSelector)),
            abi.encode(onRamp)
        );
        vm.mockCall(
            onRamp,
            abi.encodeCall(IOnRamp.getPoolBySourceToken, (destinationChainSelector, token)),
            abi.encode(recipient)
        );
        _expectBlocked(
            abi.encodeCall(
                IBridgeSettlerActions.BRIDGE_TO_CCIP, (address(bridgeDummy), _ccipData(destinationChainSelector))
            ),
            recipient
        );
    }

    function test_RecipientCheck_DefaultCCIP_DoesNotReadPool() public {
        MockERC20(address(token)).mint(address(bridgeSettler), 1 ether);
        vm.mockCall(
            address(bridgeDummy), abi.encodeWithSelector(IRouterClient.ccipSend.selector), abi.encode(bytes32(0))
        );
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(IBridgeSettlerActions.BRIDGE_TO_CCIP, (address(bridgeDummy), _ccipData(1)))
        );
        assertTrue(bridgeSettler.execute(actions, bytes32(0)));
        assertEq(token.allowance(address(bridgeSettler), address(bridgeDummy)), type(uint256).max);
    }

    function test_RecipientCheck_TempoBridge_Enabled() public {
        TempoBridgeRecipientCheckHarness tempo = new TempoBridgeRecipientCheckHarness();
        assertTrue(tempo.hasRecipientCheck());
    }

    function test_RecipientCheck_TempoRelay_NonTIP20_Transfers() public {
        TempoBridgeSettler tempo = new TempoBridgeSettler(bytes20(0));
        MockERC20(address(token)).mint(address(tempo), 1 ether);
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(IBridgeSettlerActions.BRIDGE_ERC20_TO_RELAY, (address(token), recipient, bytes32(0)))
        );
        assertTrue(tempo.execute(actions, bytes32(0)));
        assertEq(token.balanceOf(recipient), 1 ether);
        assertEq(token.balanceOf(address(tempo)), 0);
    }

    function test_RecipientCheck_TempoTransferFrom_SelfTIP20_Transfers() public {
        TempoBridgeSettler tempo = new TempoBridgeSettler(bytes20(0));
        address tip20 = 0x20C0000000000000000000000000000000000001;
        deployCodeTo("MockERC20", abi.encode("TIP20", "TIP20", 18), tip20);
        vm.etch(address(ALLOWANCE_HOLDER), vm.getDeployedCode("AllowanceHolder.sol:AllowanceHolder"));
        MockERC20(tip20).mint(address(this), 1 ether);
        IERC20(tip20).approve(address(ALLOWANCE_HOLDER), 1 ether);
        bytes[] memory actions = ActionDataBuilder.build(_getDefaultTransferFrom(address(tempo), tip20, 1 ether));
        ALLOWANCE_HOLDER.exec(
            address(tempo),
            tip20,
            1 ether,
            payable(address(tempo)),
            abi.encodeCall(tempo.execute, (actions, bytes32(0)))
        );
        assertEq(IERC20(tip20).balanceOf(address(tempo)), 1 ether);
        assertEq(IERC20(tip20).balanceOf(address(this)), 0);
    }

    function test_RecipientCheck_NativeRelay_TransfersWithoutCheck() public {
        BridgeRecipientCheckHarness checkedSettler = new BridgeRecipientCheckHarness(recipient, token);
        vm.deal(address(checkedSettler), 1 ether);
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(IBridgeSettlerActions.BRIDGE_NATIVE_TO_RELAY, (recipient, bytes32(0)))
        );
        assertTrue(checkedSettler.execute(actions, bytes32(0)));
        assertEq(recipient.balance, 1 ether);
    }

    function _expectBlocked(bytes memory action, address transferee) private {
        BridgeRecipientCheckHarness checkedSettler = new BridgeRecipientCheckHarness(transferee, token);
        MockERC20(address(token)).mint(address(checkedSettler), 1 ether);
        bytes[] memory actions = ActionDataBuilder.build(action);
        vm.expectRevert(abi.encodeWithSelector(ReceivePolicyBlocked.selector, transferee));
        checkedSettler.execute(actions, bytes32(0));
        assertEq(token.balanceOf(address(checkedSettler)), 1 ether);
        assertEq(token.balanceOf(transferee), 0);
        assertEq(token.allowance(address(checkedSettler), transferee), 0);
    }

    function _oftData() private pure returns (bytes memory) {
        IOFT.SendParam memory sendParam;
        IOFT.MessagingFee memory fee;
        return abi.encode(sendParam, fee, address(0));
    }

    function _ccipData(uint64 destinationChainSelector) private view returns (bytes memory) {
        IRouterClient.EVMTokenAmount[] memory amounts = new IRouterClient.EVMTokenAmount[](1);
        amounts[0] = IRouterClient.EVMTokenAmount(address(token), 0);
        IRouterClient.EVM2AnyMessage memory message;
        message.tokenAmounts = amounts;
        return abi.encode(destinationChainSelector, message);
    }
}

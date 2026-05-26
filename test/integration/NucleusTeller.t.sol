// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {Vm} from "@forge-std/Vm.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {BridgeSettlerIntegrationTest} from "./BridgeSettler.t.sol";
import {ALLOWANCE_HOLDER} from "src/allowanceholder/IAllowanceHolder.sol";
import {IBridgeSettlerActions} from "src/bridge/IBridgeSettlerActions.sol";
import {INucleusTeller} from "src/core/NucleusTeller.sol";
import {SafeTransferLib} from "src/vendor/SafeTransferLib.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";
import {LibBytes} from "../utils/LibBytes.sol";

contract NucleusTellerMainnetTest is BridgeSettlerIntegrationTest {
    using SafeTransferLib for IERC20;
    using LibBytes for bytes;

    // Hardcoded in NucleusTeller.sol — same address on every supported chain
    address constant TELLER = 0xeE98730AAAdA5e6e092cA69F1AC1B9B554c059dF;
    IERC20 constant WPAXG = IERC20(0x5cB5C4d5e8B184A364534bc688DA0553Ccf8F484);
    IERC20 constant PAXG = IERC20(0x45804880De22913dAFE09f4980848ECE6EcbAf78);

    // LayerZero v2 endpoint IDs (https://docs.layerzero.network/v2/deployments/deployed-contracts)
    uint32 constant OP_LZ_EID = 30111;

    // event MessageSent(bytes32 messageId, uint256 shareAmount, address to)
    bytes32 constant MESSAGE_SENT_TOPIC = 0xe0ec62d39b054dc2fd626dbc271483735df6e6fa1ef8389754bf8ab27a75eab2;

    IERC20 constant ETH_ADDRESS = IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE);

    address recipient;

    receive() external payable {}

    function _testBlockNumber() internal pure override returns (uint256) {
        return 25180132;
    }

    function setUp() public override {
        super.setUp();
        vm.label(TELLER, "Teller");
        vm.label(address(WPAXG), "WPAXG");
        vm.label(address(PAXG), "PAXG");
        recipient = makeAddr("recipient");
    }

    function _bridgeData() internal view returns (INucleusTeller.BridgeData memory) {
        return INucleusTeller.BridgeData({
            chainSelector: OP_LZ_EID,
            destinationChainReceiver: recipient,
            bridgeFeeToken: ETH_ADDRESS,
            messageGas: 100_000,
            data: bytes("")
        });
    }

    /// @dev Asserts exactly one `MessageSent(bytes32,uint256,address)` was emitted by the Teller
    /// with the given `shareAmount` and `to` fields. The `messageId` (LayerZero GUID) is unknown
    /// up front, so we decode the data manually rather than using `vm.expectEmit`.
    function _assertMessageSent(uint256 expectedShareAmount, address expectedTo) internal {
        Vm.Log[] memory logs = vm.getRecordedLogs();
        uint256 matched;
        for (uint256 i = 0; i < logs.length; i++) {
            if (logs[i].topics[0] == MESSAGE_SENT_TOPIC && logs[i].emitter == TELLER) {
                (, uint256 shareAmount, address to) = abi.decode(logs[i].data, (bytes32, uint256, address));
                assertEq(shareAmount, expectedShareAmount, "MessageSent shareAmount mismatch");
                assertEq(to, expectedTo, "MessageSent destinationChainReceiver mismatch");
                matched++;
            }
        }
        assertEq(matched, 1, "Teller MessageSent event not emitted exactly once");
    }

    function testBridge_WPAXG_to_OP() public {
        uint256 shareAmount = 1e18;

        deal(address(WPAXG), address(this), shareAmount, true);
        WPAXG.safeApprove(address(ALLOWANCE_HOLDER), shareAmount);

        INucleusTeller.BridgeData memory data = _bridgeData();
        uint256 fee = INucleusTeller(TELLER).previewFee(shareAmount, data);

        // The action overrides shareAmount with the BridgeSettler's balance; encode a 0 placeholder
        bytes memory bridgeCallData = abi.encodeCall(INucleusTeller.bridge, (0, data)).popSelector();

        bytes[] memory actions = ActionDataBuilder.build(
            _getDefaultTransferFrom(address(WPAXG), shareAmount),
            abi.encodeCall(IBridgeSettlerActions.BRIDGE_TO_NUCLEUS_TELLER, (bridgeCallData))
        );

        deal(address(this), fee);
        uint256 supplyBefore = WPAXG.totalSupply();

        vm.expectCall(TELLER, fee, abi.encodeCall(INucleusTeller.bridge, (shareAmount, data)));
        vm.recordLogs();
        ALLOWANCE_HOLDER.exec{value: fee}(
            address(bridgeSettler),
            address(WPAXG),
            shareAmount,
            payable(address(bridgeSettler)),
            abi.encodeCall(bridgeSettler.execute, (actions, bytes32(0)))
        );

        _assertMessageSent(shareAmount, recipient);
        assertEq(WPAXG.balanceOf(address(bridgeSettler)), 0, "BridgeSettler should hold no WPAXG after bridge");
        assertEq(WPAXG.totalSupply(), supplyBefore - shareAmount, "Shares should have been burned");
        assertEq(address(bridgeSettler).balance, 0, "BridgeSettler should have forwarded the full fee");
    }

    function testBridge_WPAXG_to_OP_refundsExcessFee() public {
        uint256 shareAmount = 1e18;

        deal(address(WPAXG), address(this), shareAmount, true);
        WPAXG.safeApprove(address(ALLOWANCE_HOLDER), shareAmount);

        INucleusTeller.BridgeData memory data = _bridgeData();
        uint256 fee = INucleusTeller(TELLER).previewFee(shareAmount, data);
        uint256 excess = 0.1 ether;

        bytes memory bridgeCallData = abi.encodeCall(INucleusTeller.bridge, (0, data)).popSelector();
        bytes[] memory actions = ActionDataBuilder.build(
            _getDefaultTransferFrom(address(WPAXG), shareAmount),
            abi.encodeCall(IBridgeSettlerActions.BRIDGE_TO_NUCLEUS_TELLER, (bridgeCallData))
        );

        deal(address(this), fee + excess);
        uint256 supplyBefore = WPAXG.totalSupply();

        vm.recordLogs();
        ALLOWANCE_HOLDER.exec{value: fee + excess}(
            address(bridgeSettler),
            address(WPAXG),
            shareAmount,
            payable(address(bridgeSettler)),
            abi.encodeCall(bridgeSettler.execute, (actions, bytes32(0)))
        );

        _assertMessageSent(shareAmount, recipient);
        assertEq(WPAXG.totalSupply(), supplyBefore - shareAmount, "Bridge should have completed");
        // LayerZero refunds excess to the Teller's `payable(msg.sender)` — i.e. BridgeSettler.
        assertEq(address(bridgeSettler).balance, excess, "Excess should be refunded back to BridgeSettler");
    }

    function testDepositAndBridge_PAXG_to_OP() public {
        uint256 depositAmount = 1e18;

        deal(address(PAXG), address(this), depositAmount, true);
        PAXG.safeApprove(address(ALLOWANCE_HOLDER), depositAmount);

        INucleusTeller.BridgeData memory data = _bridgeData();
        // PAXG → WPAXG is a 1:1 wrap, so the resulting share count equals the deposit amount.
        uint256 expectedShares = depositAmount;
        uint256 fee = INucleusTeller(TELLER).previewFee(expectedShares, data);

        // Encode `(2, 1)` — the action should scale `minimumMint` to `depositAmount / 2`,
        // preserving the 1:2 ratio of accepted shares to deposit asset.
        bytes memory depositAndBridgeCallData =
            abi.encodeCall(INucleusTeller.depositAndBridge, (PAXG, 2, 1, data)).popSelector();

        bytes[] memory actions = ActionDataBuilder.build(
            _getDefaultTransferFrom(address(PAXG), depositAmount),
            abi.encodeCall(IBridgeSettlerActions.DEPOSIT_AND_BRIDGE_TO_NUCLEUS_TELLER, (depositAndBridgeCallData))
        );

        deal(address(this), fee);

        vm.expectCall(
            TELLER, fee, abi.encodeCall(INucleusTeller.depositAndBridge, (PAXG, depositAmount, depositAmount / 2, data))
        );
        vm.recordLogs();
        ALLOWANCE_HOLDER.exec{value: fee}(
            address(bridgeSettler),
            address(PAXG),
            depositAmount,
            payable(address(bridgeSettler)),
            abi.encodeCall(bridgeSettler.execute, (actions, bytes32(0)))
        );

        _assertMessageSent(expectedShares, recipient);
        assertEq(PAXG.balanceOf(address(bridgeSettler)), 0, "BridgeSettler should hold no PAXG after");
        assertEq(WPAXG.balanceOf(address(bridgeSettler)), 0, "BridgeSettler should hold no WPAXG after bridge");
        assertEq(address(bridgeSettler).balance, 0, "BridgeSettler should have forwarded the full fee");
    }
}

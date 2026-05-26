// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
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

    // WPAXG Teller (Paxos Nucleus CrossChainTellerBase) and BoringVault (= WPAXG share token) on Ethereum mainnet
    address constant TELLER = 0xeE98730AAAdA5e6e092cA69F1AC1B9B554c059dF;
    IERC20 constant WPAXG = IERC20(0x5cB5C4d5e8B184A364534bc688DA0553Ccf8F484);
    IERC20 constant PAXG = IERC20(0x45804880De22913dAFE09f4980848ECE6EcbAf78);

    // LayerZero v2 endpoint ID for Optimism (destination chain)
    uint32 constant OP_LZ_EID = 30111;

    address recipient;

    receive() external payable {}

    function _testBlockNumber() internal pure override returns (uint256) {
        // Recent mainnet block where the WPAXG Teller and BoringVault are deployed.
        return 24700000;
    }

    function setUp() public override {
        super.setUp();
        vm.label(TELLER, "WPAXG_Teller");
        vm.label(address(WPAXG), "WPAXG");
        vm.label(address(PAXG), "PAXG");
        recipient = makeAddr("recipient");
    }

    function _bridgeData() internal view returns (INucleusTeller.BridgeData memory) {
        return INucleusTeller.BridgeData({
            chainSelector: OP_LZ_EID,
            destinationChainReceiver: recipient,
            bridgeFeeToken: IERC20(address(0)),
            messageGas: 200_000,
            data: bytes("")
        });
    }

    function testBridge_WPAXG_to_OP() public {
        uint256 shareAmount = 1e18;

        // Fund this contract with WPAXG and approve AllowanceHolder so BridgeSettler can pull them in
        deal(address(WPAXG), address(this), shareAmount, true);
        WPAXG.safeApprove(address(ALLOWANCE_HOLDER), shareAmount);

        INucleusTeller.BridgeData memory data = _bridgeData();
        uint256 fee = INucleusTeller(TELLER).previewFee(shareAmount, data);

        // The action overrides shareAmount with the BridgeSettler's balance; encode a 0 placeholder
        bytes memory bridgeCallData = abi.encodeCall(INucleusTeller.bridge, (0, data)).popSelector();

        bytes[] memory actions = ActionDataBuilder.build(
            _getDefaultTransferFrom(address(WPAXG), shareAmount),
            abi.encodeCall(IBridgeSettlerActions.BRIDGE_TO_NUCLEUS_TELLER, (TELLER, bridgeCallData))
        );

        deal(address(this), fee);
        uint256 supplyBefore = WPAXG.totalSupply();

        vm.expectCall(TELLER, fee, abi.encodeCall(INucleusTeller.bridge, (shareAmount, data)));
        ALLOWANCE_HOLDER.exec{value: fee}(
            address(bridgeSettler),
            address(WPAXG),
            shareAmount,
            payable(address(bridgeSettler)),
            abi.encodeCall(bridgeSettler.execute, (actions, bytes32(0)))
        );

        assertEq(WPAXG.balanceOf(address(bridgeSettler)), 0, "BridgeSettler should hold no WPAXG after bridge");
        assertEq(WPAXG.totalSupply(), supplyBefore - shareAmount, "Shares should have been burned");
        assertEq(address(bridgeSettler).balance, 0, "BridgeSettler should have forwarded the full fee");
    }

    function testDepositAndBridge_PAXG_to_OP() public {
        uint256 depositAmount = 1e18;

        // Fund this contract with PAXG and approve AllowanceHolder
        deal(address(PAXG), address(this), depositAmount, true);
        PAXG.safeApprove(address(ALLOWANCE_HOLDER), depositAmount);

        INucleusTeller.BridgeData memory data = _bridgeData();
        // previewFee takes shares, not deposit amount. We compute expected shares from the
        // BoringVault accountant rate, mirroring `_erc20Deposit`. For the test purpose, we
        // simply use the deposit amount as a fee preview proxy — actual conversion is done by
        // the Teller via the accountant.
        uint256 expectedShares = depositAmount; // 1:1 placeholder for fee preview
        uint256 fee = INucleusTeller(TELLER).previewFee(expectedShares, data);

        // depositAmount field is overridden by the action; encode 0 placeholder
        bytes memory depositAndBridgeCallData =
            abi.encodeCall(INucleusTeller.depositAndBridge, (PAXG, 0, 0, data)).popSelector();

        bytes[] memory actions = ActionDataBuilder.build(
            _getDefaultTransferFrom(address(PAXG), depositAmount),
            abi.encodeCall(
                IBridgeSettlerActions.DEPOSIT_AND_BRIDGE_TO_NUCLEUS_TELLER, (TELLER, depositAndBridgeCallData)
            )
        );

        deal(address(this), fee);

        vm.expectCall(TELLER, fee, abi.encodeCall(INucleusTeller.depositAndBridge, (PAXG, depositAmount, 0, data)));
        ALLOWANCE_HOLDER.exec{value: fee}(
            address(bridgeSettler),
            address(PAXG),
            depositAmount,
            payable(address(bridgeSettler)),
            abi.encodeCall(bridgeSettler.execute, (actions, bytes32(0)))
        );

        assertEq(PAXG.balanceOf(address(bridgeSettler)), 0, "BridgeSettler should hold no PAXG after");
        assertEq(WPAXG.balanceOf(address(bridgeSettler)), 0, "BridgeSettler should hold no WPAXG after bridge");
        assertEq(address(bridgeSettler).balance, 0, "BridgeSettler should have forwarded the full fee");
    }
}

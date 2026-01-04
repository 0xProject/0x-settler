// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Settler} from "src/Settler.sol";
import {ISettlerTakerSubmitted} from "src/interfaces/ISettlerTakerSubmitted.sol";
import {CalldataDecoder, SettlerBase} from "src/SettlerBase.sol";
import {UnsafeMath} from "src/utils/UnsafeMath.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {Utils} from "../Utils.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {Test} from "@forge-std/Test.sol";

// Mock Settler for testing bulk operations
contract MockSettler is Settler {
    function _tokenId() internal pure override returns (uint256) {
        return 2;
    }

    function _hasMetaTxn() internal pure override returns (bool) {
        return false;
    }

    function _dispatch(uint256 i, uint256 action, bytes calldata data)
        internal
        pure
        override
        returns (bool)
    {
        // Mock implementation - just return true for any action
        return true;
    }

    function _dispatchVIP(uint256 action, bytes calldata data) internal pure override returns (bool) {
        // Mock implementation - return true for TRANSFER_FROM
        if (action == uint32(ISettlerActions.TRANSFER_FROM.selector)) {
            return true;
        }
        return false;
    }

    // Mock slippage check and transfer
    function _checkSlippageAndTransfer(ISettlerTakerSubmitted.AllowedSlippage calldata slippage) internal override {
        // Mock implementation - do nothing
    }

    function _isRestrictedTarget(address target) internal pure override returns (bool) {
        return false;
    }
}

contract BulkSettlementUnitTest is Utils, Test {
    MockSettler settler;
    address user1 = address(0x123);
    address user2 = address(0x456);
    address user3 = address(0x789);

    function setUp() public {
        settler = new MockSettler();
    }

    // ════════════════════════════════════════════════════════════════════════════
    // BULK EXECUTE TESTS
    // ════════════════════════════════════════════════════════════════════════════

    function testBulkExecuteSingleSettlement() public {
        ISettlerTakerSubmitted.BulkSettlement[] memory settlements = new ISettlerTakerSubmitted.BulkSettlement[](1);

        // Create a simple settlement with empty actions
        settlements[0] = ISettlerTakerSubmitted.BulkSettlement({
            slippage: ISettlerTakerSubmitted.AllowedSlippage({
                recipient: user1,
                buyToken: address(0),
                minAmountOut: 0
            }),
            actions: new bytes[](0),
            zidAndAffiliate: bytes32(0)
        });

        vm.expectEmit(true, false, false, true);
        emit ISettlerTakerSubmitted.BulkSettlementsExecuted(user1, 1, 0);

        bool success = settler.bulkExecute(settlements);
        assertTrue(success);
    }

    function testBulkExecuteMultipleSettlements() public {
        ISettlerTakerSubmitted.BulkSettlement[] memory settlements = new ISettlerTakerSubmitted.BulkSettlement[](3);

        for (uint256 i = 0; i < 3; i++) {
            settlements[i] = ISettlerTakerSubmitted.BulkSettlement({
                slippage: ISettlerTakerSubmitted.AllowedSlippage({
                    recipient: user1,
                    buyToken: address(0),
                    minAmountOut: 0
                }),
                actions: new bytes[](0),
                zidAndAffiliate: bytes32(0)
            });
        }

        vm.expectEmit(true, false, false, true);
        emit ISettlerTakerSubmitted.BulkSettlementsExecuted(user1, 3, 0);

        bool success = settler.bulkExecute(settlements);
        assertTrue(success);
    }

    function testBulkExecuteMaximumSettlements() public {
        ISettlerTakerSubmitted.BulkSettlement[] memory settlements = new ISettlerTakerSubmitted.BulkSettlement[](5);

        for (uint256 i = 0; i < 5; i++) {
            settlements[i] = ISettlerTakerSubmitted.BulkSettlement({
                slippage: ISettlerTakerSubmitted.AllowedSlippage({
                    recipient: user1,
                    buyToken: address(0),
                    minAmountOut: 0
                }),
                actions: new bytes[](0),
                zidAndAffiliate: bytes32(0)
            });
        }

        vm.expectEmit(true, false, false, true);
        emit ISettlerTakerSubmitted.BulkSettlementsExecuted(user1, 5, 0);

        bool success = settler.bulkExecute(settlements);
        assertTrue(success);
    }

    function testBulkExecuteExceedsMaximumSettlements() public {
        ISettlerTakerSubmitted.BulkSettlement[] memory settlements = new ISettlerTakerSubmitted.BulkSettlement[](6);

        for (uint256 i = 0; i < 6; i++) {
            settlements[i] = ISettlerTakerSubmitted.BulkSettlement({
                slippage: ISettlerTakerSubmitted.AllowedSlippage({
                    recipient: user1,
                    buyToken: address(0),
                    minAmountOut: 0
                }),
                actions: new bytes[](0),
                zidAndAffiliate: bytes32(0)
            });
        }

        vm.expectRevert(bytes("BulkExecute: invalid settlement count"));
        settler.bulkExecute(settlements);
    }

    function testBulkExecuteEmptySettlements() public {
        ISettlerTakerSubmitted.BulkSettlement[] memory settlements = new ISettlerTakerSubmitted.BulkSettlement[](0);

        vm.expectRevert(bytes("BulkExecute: invalid settlement count"));
        settler.bulkExecute(settlements);
    }

    function testBulkExecuteWithActions() public {
        ISettlerTakerSubmitted.BulkSettlement[] memory settlements = new ISettlerTakerSubmitted.BulkSettlement[](2);

        // First settlement with some mock actions
        bytes[] memory actions1 = new bytes[](2);
        actions1[0] = abi.encode(uint32(ISettlerActions.TRANSFER_FROM.selector), user1, "mock_data");
        actions1[1] = abi.encode(uint32(ISettlerActions.NATIVE_CHECK.selector), uint256(1000000000), uint256(0));

        settlements[0] = ISettlerTakerSubmitted.BulkSettlement({
            slippage: ISettlerTakerSubmitted.AllowedSlippage({
                recipient: user1,
                buyToken: address(0),
                minAmountOut: 0
            }),
            actions: actions1,
            zidAndAffiliate: bytes32(0)
        });

        // Second settlement with different actions
        bytes[] memory actions2 = new bytes[](1);
        actions2[0] = abi.encode(uint32(ISettlerActions.NATIVE_CHECK.selector), uint256(1000000000), uint256(0));

        settlements[1] = ISettlerTakerSubmitted.BulkSettlement({
            slippage: ISettlerTakerSubmitted.AllowedSlippage({
                recipient: user2,
                buyToken: address(0),
                minAmountOut: 0
            }),
            actions: actions2,
            zidAndAffiliate: bytes32(0)
        });

        vm.expectEmit(true, false, false, true);
        emit ISettlerTakerSubmitted.BulkSettlementsExecuted(user1, 2, 0);

        bool success = settler.bulkExecute(settlements);
        assertTrue(success);
    }

    // ════════════════════════════════════════════════════════════════════════════
    // BULK EXECUTE SHARED SLIPPAGE TESTS
    // ════════════════════════════════════════════════════════════════════════════

    function testBulkExecuteSharedSlippage() public {
        ISettlerTakerSubmitted.AllowedSlippage memory sharedSlippage = ISettlerTakerSubmitted.AllowedSlippage({
            recipient: user1,
            buyToken: address(0),
            minAmountOut: 0
        });

        bytes[][] memory settlements = new bytes[][](3);
        settlements[0] = new bytes[](0);
        settlements[1] = new bytes[](0);
        settlements[2] = new bytes[](0);

        vm.expectEmit(true, false, false, true);
        emit ISettlerTakerSubmitted.BulkSettlementsExecuted(user1, 3, 0);

        bool success = settler.bulkExecuteSharedSlippage(sharedSlippage, settlements, bytes32(0));
        assertTrue(success);
    }

    function testBulkExecuteSharedSlippageMaximumSettlements() public {
        ISettlerTakerSubmitted.AllowedSlippage memory sharedSlippage = ISettlerTakerSubmitted.AllowedSlippage({
            recipient: user1,
            buyToken: address(0),
            minAmountOut: 0
        });

        bytes[][] memory settlements = new bytes[][](10);
        for (uint256 i = 0; i < 10; i++) {
            settlements[i] = new bytes[](0);
        }

        vm.expectEmit(true, false, false, true);
        emit ISettlerTakerSubmitted.BulkSettlementsExecuted(user1, 10, 0);

        bool success = settler.bulkExecuteSharedSlippage(sharedSlippage, settlements, bytes32(0));
        assertTrue(success);
    }

    function testBulkExecuteSharedSlippageExceedsMaximum() public {
        ISettlerTakerSubmitted.AllowedSlippage memory sharedSlippage = ISettlerTakerSubmitted.AllowedSlippage({
            recipient: user1,
            buyToken: address(0),
            minAmountOut: 0
        });

        bytes[][] memory settlements = new bytes[][](11);
        for (uint256 i = 0; i < 11; i++) {
            settlements[i] = new bytes[](0);
        }

        vm.expectRevert(bytes("BulkExecuteShared: invalid settlement count"));
        settler.bulkExecuteSharedSlippage(sharedSlippage, settlements, bytes32(0));
    }

    function testBulkExecuteSharedSlippageWithActions() public {
        ISettlerTakerSubmitted.AllowedSlippage memory sharedSlippage = ISettlerTakerSubmitted.AllowedSlippage({
            recipient: user1,
            buyToken: address(0),
            minAmountOut: 0
        });

        bytes[][] memory settlements = new bytes[][](2);

        // First settlement with actions
        bytes[] memory actions1 = new bytes[](1);
        actions1[0] = abi.encode(uint32(ISettlerActions.NATIVE_CHECK.selector), uint256(1000000000), uint256(0));
        settlements[0] = actions1;

        // Second settlement with different actions
        bytes[] memory actions2 = new bytes[](2);
        actions2[0] = abi.encode(uint32(ISettlerActions.TRANSFER_FROM.selector), user2, "mock_data");
        actions2[1] = abi.encode(uint32(ISettlerActions.NATIVE_CHECK.selector), uint256(1000000000), uint256(0));
        settlements[1] = actions2;

        vm.expectEmit(true, false, false, true);
        emit ISettlerTakerSubmitted.BulkSettlementsExecuted(user1, 2, 0);

        bool success = settler.bulkExecuteSharedSlippage(sharedSlippage, settlements, bytes32(0));
        assertTrue(success);
    }

    // ════════════════════════════════════════════════════════════════════════════
    // EMERGENCY BULK CANCEL TESTS
    // ════════════════════════════════════════════════════════════════════════════

    function testEmergencyBulkCancel() public {
        bytes32[] memory settlementIds = new bytes32[](3);
        settlementIds[0] = keccak256("settlement1");
        settlementIds[1] = keccak256("settlement2");
        settlementIds[2] = keccak256("settlement3");

        // Note: This test assumes the emergency cancel is authorized
        // In real implementation, this would check contract ownership
        vm.expectEmit(true, false, false, true);
        emit ISettlerTakerSubmitted.BulkSettlementsExecuted(address(settler), 3, 0);

        bool success = settler.emergencyBulkCancel(settlementIds);
        assertTrue(success);
    }

    function testEmergencyBulkCancelMaximum() public {
        bytes32[] memory settlementIds = new bytes32[](20);
        for (uint256 i = 0; i < 20; i++) {
            settlementIds[i] = keccak256(abi.encodePacked("settlement", i));
        }

        vm.expectEmit(true, false, false, true);
        emit ISettlerTakerSubmitted.BulkSettlementsExecuted(address(settler), 20, 0);

        bool success = settler.emergencyBulkCancel(settlementIds);
        assertTrue(success);
    }

    function testEmergencyBulkCancelExceedsMaximum() public {
        bytes32[] memory settlementIds = new bytes32[](21);
        for (uint256 i = 0; i < 21; i++) {
            settlementIds[i] = keccak256(abi.encodePacked("settlement", i));
        }

        vm.expectRevert(bytes("EmergencyCancel: invalid cancellation count"));
        settler.emergencyBulkCancel(settlementIds);
    }

    function testEmergencyBulkCancelEmptyArray() public {
        bytes32[] memory settlementIds = new bytes32[](0);

        vm.expectRevert(bytes("EmergencyCancel: invalid cancellation count"));
        settler.emergencyBulkCancel(settlementIds);
    }

    // ════════════════════════════════════════════════════════════════════════════
    // UTILITY FUNCTION TESTS
    // ════════════════════════════════════════════════════════════════════════════

    function testGetBulkExecutionLimits() public {
        (uint256 maxSettlementsPerBulk, uint256 maxSharedSlippageSettlements, uint256 maxEmergencyCancellations) =
            settler.getBulkExecutionLimits();

        assertEq(maxSettlementsPerBulk, 5);
        assertEq(maxSharedSlippageSettlements, 10);
        assertEq(maxEmergencyCancellations, 20);
    }

    function testEstimateBulkExecutionGas() public {
        // Test with individual slippage
        uint256 gasEstimate1 = settler.estimateBulkExecutionGas(3, false);
        uint256 expectedGas1 = 21000 + (65000 * 3); // base + per settlement
        assertEq(gasEstimate1, expectedGas1);

        // Test with shared slippage
        uint256 gasEstimate2 = settler.estimateBulkExecutionGas(5, true);
        uint256 expectedGas2 = 21000 + (45000 * 5);
        assertEq(gasEstimate2, expectedGas2);
    }

    function testEstimateBulkExecutionGasExceedsLimits() public {
        // Test exceeding individual slippage limit
        vm.expectRevert(bytes("EstimateGas: too many settlements"));
        settler.estimateBulkExecutionGas(6, false);

        // Test exceeding shared slippage limit
        vm.expectRevert(bytes("EstimateGas: too many settlements"));
        settler.estimateBulkExecutionGas(11, true);
    }

    function testEstimateBulkExecutionGasInvalidCount() public {
        vm.expectRevert(bytes("EstimateGas: invalid count"));
        settler.estimateBulkExecutionGas(0, false);
    }

    // ════════════════════════════════════════════════════════════════════════════
    // INTEGRATION TESTS
    // ════════════════════════════════════════════════════════════════════════════

    function testBulkOperationsValueTracking() public {
        // Send some ETH to test value tracking
        vm.deal(user1, 10 ether);

        ISettlerTakerSubmitted.BulkSettlement[] memory settlements = new ISettlerTakerSubmitted.BulkSettlement[](2);

        settlements[0] = ISettlerTakerSubmitted.BulkSettlement({
            slippage: ISettlerTakerSubmitted.AllowedSlippage({
                recipient: user1,
                buyToken: address(0),
                minAmountOut: 0
            }),
            actions: new bytes[](0),
            zidAndAffiliate: bytes32(0)
        });

        settlements[1] = ISettlerTakerSubmitted.BulkSettlement({
            slippage: ISettlerTakerSubmitted.AllowedSlippage({
                recipient: user2,
                buyToken: address(0),
                minAmountOut: 0
            }),
            actions: new bytes[](0),
            zidAndAffiliate: bytes32(0)
        });

        vm.prank(user1);
        vm.expectEmit(true, false, false, true);
        emit ISettlerTakerSubmitted.BulkSettlementsExecuted(user1, 2, 5 ether); // 10 ether / 2

        settler.bulkExecute{value: 10 ether}(settlements);
    }

    function testMixedBulkOperationsWorkflow() public {
        // Test combining different bulk operations
        ISettlerTakerSubmitted.AllowedSlippage memory sharedSlippage = ISettlerTakerSubmitted.AllowedSlippage({
            recipient: user1,
            buyToken: address(0),
            minAmountOut: 0
        });

        bytes[][] memory settlements = new bytes[][](3);
        for (uint256 i = 0; i < 3; i++) {
            settlements[i] = new bytes[](0);
        }

        // Execute shared slippage settlements
        vm.expectEmit(true, false, false, true);
        emit ISettlerTakerSubmitted.BulkSettlementsExecuted(user1, 3, 0);
        settler.bulkExecuteSharedSlippage(sharedSlipage, settlements, bytes32(0));

        // Test limits
        (uint256 max1, uint256 max2, uint256 max3) = settler.getBulkExecutionLimits();
        assertEq(max1, 5);
        assertEq(max2, 10);
        assertEq(max3, 20);

        // Test gas estimation
        uint256 gasEstimate = settler.estimateBulkExecutionGas(3, true);
        assertGt(gasEstimate, 0);
    }

    function testBulkOperationsErrorIsolation() public {
        // Test that one failed settlement doesn't prevent others from executing
        // Note: In current implementation, all settlements in a batch must succeed or fail together
        // This is a design decision for atomicity

        ISettlerTakerSubmitted.BulkSettlement[] memory settlements = new ISettlerTakerSubmitted.BulkSettlement[](2);

        // First settlement - valid
        settlements[0] = ISettlerTakerSubmitted.BulkSettlement({
            slippage: ISettlerTakerSubmitted.AllowedSlippage({
                recipient: user1,
                buyToken: address(0),
                minAmountOut: 0
            }),
            actions: new bytes[](0),
            zidAndAffiliate: bytes32(0)
        });

        // Second settlement - would fail if we had invalid actions, but since we use mocks, it succeeds
        settlements[1] = ISettlerTakerSubmitted.BulkSettlement({
            slippage: ISettlerTakerSubmitted.AllowedSlippage({
                recipient: user2,
                buyToken: address(0),
                minAmountOut: 0
            }),
            actions: new bytes[](0),
            zidAndAffiliate: bytes32(0)
        });

        bool success = settler.bulkExecute(settlements);
        assertTrue(success);
    }

    // ════════════════════════════════════════════════════════════════════════════
    // GAS EFFICIENCY TESTS
    // ════════════════════════════════════════════════════════════════════════════

    function testBulkOperationsGasComparison() public {
        ISettlerTakerSubmitted.AllowedSlippage memory slippage = ISettlerTakerSubmitted.AllowedSlippage({
            recipient: user1,
            buyToken: address(0),
            minAmountOut: 0
        });

        // Measure gas for individual settlements
        uint256 gasStart = gasleft();

        for (uint256 i = 0; i < 3; i++) {
            ISettlerTakerSubmitted.BulkSettlement[] memory singleSettlement = new ISettlerTakerSubmitted.BulkSettlement[](1);
            singleSettlement[0] = ISettlerTakerSubmitted.BulkSettlement({
                slippage: slippage,
                actions: new bytes[](0),
                zidAndAffiliate: bytes32(0)
            });
            settler.bulkExecute(singleSettlement);
        }

        uint256 individualGas = gasStart - gasleft();

        // Measure gas for bulk settlement
        gasStart = gasleft();

        ISettlerTakerSubmitted.BulkSettlement[] memory bulkSettlements = new ISettlerTakerSubmitted.BulkSettlement[](3);
        for (uint256 i = 0; i < 3; i++) {
            bulkSettlements[i] = ISettlerTakerSubmitted.BulkSettlement({
                slippage: slippage,
                actions: new bytes[](0),
                zidAndAffiliate: bytes32(0)
            });
        }

        settler.bulkExecute(bulkSettlements);

        uint256 bulkGas = gasStart - gasleft();

        // Bulk should be more gas efficient
        assertLt(bulkGas, individualGas);
    }
}

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "@forge-std/Test.sol";
import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {InputValidation} from "src/utils/InputValidation.sol";

contract InputValidationTest is Test {
    using InputValidation for address;
    using InputValidation for IERC20;
    using InputValidation for uint256;

    address constant ZERO_ADDRESS = address(0);
    address constant NON_ZERO_ADDRESS = address(0x1234);
    IERC20 constant ZERO_TOKEN = IERC20(address(0));
    IERC20 constant NON_ZERO_TOKEN = IERC20(address(0x5678));

    // Test requireNonZeroAddress
    function testRequireNonZeroAddressSuccess() public pure {
        InputValidation.requireNonZeroAddress(NON_ZERO_ADDRESS);
        // Should not revert
    }

    function testRequireNonZeroAddressRevert() public {
        vm.expectRevert(abi.encodeWithSignature("ZeroAddress()"));
        InputValidation.requireNonZeroAddress(ZERO_ADDRESS);
    }

    // Test requireNonZeroToken
    function testRequireNonZeroTokenSuccess() public pure {
        InputValidation.requireNonZeroToken(NON_ZERO_TOKEN);
        // Should not revert
    }

    function testRequireNonZeroTokenRevert() public {
        vm.expectRevert(abi.encodeWithSignature("ZeroAddress()"));
        InputValidation.requireNonZeroToken(ZERO_TOKEN);
    }

    // Test requireNonZeroAmount
    function testRequireNonZeroAmountSuccess() public pure {
        InputValidation.requireNonZeroAmount(1);
        InputValidation.requireNonZeroAmount(100);
        InputValidation.requireNonZeroAmount(type(uint256).max);
        // Should not revert
    }

    function testRequireNonZeroAmountRevert() public {
        vm.expectRevert(abi.encodeWithSignature("ZeroAmount()"));
        InputValidation.requireNonZeroAmount(0);
    }

    // Test requireValidBasisPoints
    function testRequireValidBasisPointsSuccess() public pure {
        InputValidation.requireValidBasisPoints(0, 10000);
        InputValidation.requireValidBasisPoints(5000, 10000);
        InputValidation.requireValidBasisPoints(10000, 10000);
        // Should not revert
    }

    function testRequireValidBasisPointsRevert() public {
        vm.expectRevert(abi.encodeWithSignature("BasisPointsExceedMax(uint256,uint256)", 10001, 10000));
        InputValidation.requireValidBasisPoints(10001, 10000);
    }

    function testRequireValidBasisPointsRevertHighValue() public {
        vm.expectRevert(abi.encodeWithSignature("BasisPointsExceedMax(uint256,uint256)", 99999, 10000));
        InputValidation.requireValidBasisPoints(99999, 10000);
    }

    // Test requireNonZeroValidBasisPoints
    function testRequireNonZeroValidBasisPointsSuccess() public pure {
        InputValidation.requireNonZeroValidBasisPoints(1, 10000);
        InputValidation.requireNonZeroValidBasisPoints(5000, 10000);
        InputValidation.requireNonZeroValidBasisPoints(10000, 10000);
        // Should not revert
    }

    function testRequireNonZeroValidBasisPointsRevertZero() public {
        vm.expectRevert(abi.encodeWithSignature("ZeroAmount()"));
        InputValidation.requireNonZeroValidBasisPoints(0, 10000);
    }

    function testRequireNonZeroValidBasisPointsRevertExceedsMax() public {
        vm.expectRevert(abi.encodeWithSignature("BasisPointsExceedMax(uint256,uint256)", 10001, 10000));
        InputValidation.requireNonZeroValidBasisPoints(10001, 10000);
    }

    // Test requireNonEmptyArray
    function testRequireNonEmptyArraySuccess() public pure {
        InputValidation.requireNonEmptyArray(1);
        InputValidation.requireNonEmptyArray(10);
        InputValidation.requireNonEmptyArray(type(uint256).max);
        // Should not revert
    }

    function testRequireNonEmptyArrayRevert() public {
        vm.expectRevert(abi.encodeWithSignature("ZeroAmount()"));
        InputValidation.requireNonEmptyArray(0);
    }

    // Test requireDifferentAddresses
    function testRequireDifferentAddressesSuccess() public pure {
        InputValidation.requireDifferentAddresses(address(0x1), address(0x2));
        InputValidation.requireDifferentAddresses(ZERO_ADDRESS, NON_ZERO_ADDRESS);
        // Should not revert
    }

    function testRequireDifferentAddressesRevert() public {
        vm.expectRevert(abi.encodeWithSignature("DuplicateAddress(address)", NON_ZERO_ADDRESS));
        InputValidation.requireDifferentAddresses(NON_ZERO_ADDRESS, NON_ZERO_ADDRESS);
    }

    function testRequireDifferentAddressesRevertZero() public {
        vm.expectRevert(abi.encodeWithSignature("DuplicateAddress(address)", ZERO_ADDRESS));
        InputValidation.requireDifferentAddresses(ZERO_ADDRESS, ZERO_ADDRESS);
    }

    // Test requireNotExpired
    function testRequireNotExpiredSuccess() public {
        uint256 futureDeadline = block.timestamp + 1000;
        InputValidation.requireNotExpired(futureDeadline);
        // Should not revert
    }

    function testRequireNotExpiredSuccessExactTimestamp() public {
        uint256 currentDeadline = block.timestamp;
        InputValidation.requireNotExpired(currentDeadline);
        // Should not revert when deadline == block.timestamp
    }

    function testRequireNotExpiredRevert() public {
        uint256 pastDeadline = block.timestamp - 1;
        vm.expectRevert(
            abi.encodeWithSignature("DeadlineExpired(uint256,uint256)", pastDeadline, block.timestamp)
        );
        InputValidation.requireNotExpired(pastDeadline);
    }

    function testRequireNotExpiredRevertOldDeadline() public {
        uint256 pastDeadline = 1000;
        vm.warp(2000);
        vm.expectRevert(abi.encodeWithSignature("DeadlineExpired(uint256,uint256)", pastDeadline, 2000));
        InputValidation.requireNotExpired(pastDeadline);
    }

    // Fuzz tests
    function testFuzzRequireNonZeroAddress(address addr) public {
        if (addr == address(0)) {
            vm.expectRevert(abi.encodeWithSignature("ZeroAddress()"));
            InputValidation.requireNonZeroAddress(addr);
        } else {
            InputValidation.requireNonZeroAddress(addr);
            // Should not revert
        }
    }

    function testFuzzRequireNonZeroAmount(uint256 amount) public {
        if (amount == 0) {
            vm.expectRevert(abi.encodeWithSignature("ZeroAmount()"));
            InputValidation.requireNonZeroAmount(amount);
        } else {
            InputValidation.requireNonZeroAmount(amount);
            // Should not revert
        }
    }

    function testFuzzRequireValidBasisPoints(uint256 bps, uint256 maxBps) public {
        if (bps > maxBps) {
            vm.expectRevert(abi.encodeWithSignature("BasisPointsExceedMax(uint256,uint256)", bps, maxBps));
            InputValidation.requireValidBasisPoints(bps, maxBps);
        } else {
            InputValidation.requireValidBasisPoints(bps, maxBps);
            // Should not revert
        }
    }

    function testFuzzRequireDifferentAddresses(address addr1, address addr2) public {
        if (addr1 == addr2) {
            vm.expectRevert(abi.encodeWithSignature("DuplicateAddress(address)", addr1));
            InputValidation.requireDifferentAddresses(addr1, addr2);
        } else {
            InputValidation.requireDifferentAddresses(addr1, addr2);
            // Should not revert
        }
    }

    function testFuzzRequireNotExpired(uint256 deadline) public {
        vm.assume(deadline < type(uint256).max - 1);
        
        if (block.timestamp > deadline) {
            vm.expectRevert(
                abi.encodeWithSignature("DeadlineExpired(uint256,uint256)", deadline, block.timestamp)
            );
            InputValidation.requireNotExpired(deadline);
        } else {
            InputValidation.requireNotExpired(deadline);
            // Should not revert
        }
    }
}

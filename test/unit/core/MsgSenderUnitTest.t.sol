// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "@forge-std/Test.sol";

/// @dev Interface for the msgSender() external function (from src/interfaces/IMsgSender.sol)
interface IMsgSender {
    function msgSender() external view returns (address);
}

/// @title MsgSender Unit Tests
/// @notice Unit tests for the msgSender() function on Base Settler
/// @dev msgSender() is implemented via BaseMixin._fallback() and returns the current payer holding the lock
contract MsgSenderUnitTest is Test {
    /// @dev The _PAYER_SLOT from TransientStorage (Permit2Payment.sol:45)
    bytes32 private constant _PAYER_SLOT = 0x0000000000000000000000000000000000000000cd1e9517bb0cb8d0d5cde893;

    MsgSenderStub internal settler;

    function setUp() public {
        settler = new MsgSenderStub();
    }

    /// @notice Test that msgSender() reverts when no payer is set (lock not held)
    function test_msgSender_RevertsWhenNoPayerSet() public {
        // Ensure payer slot is clear
        settler.clearPayer();

        // msgSender() should revert when no lock is held
        vm.expectRevert();
        settler.msgSender();
    }

    /// @notice Test that msgSender() returns the payer when lock is held
    function test_msgSender_ReturnsPayerWhenSet() public {
        address testPayer = makeAddr("testPayer");

        // Set the payer in transient storage
        settler.setPayer(testPayer);

        // msgSender should return the payer
        address sender = settler.msgSender();
        assertEq(sender, testPayer, "msgSender should return the payer address");

        // Cleanup
        settler.clearPayer();
    }

    /// @notice Fuzz test that msgSender() correctly returns the payer address
    function testFuzz_msgSender_ReturnsCorrectPayer(address payer) public {
        vm.assume(payer != address(0));

        settler.setPayer(payer);
        address sender = settler.msgSender();
        assertEq(sender, payer, "msgSender should return the set payer address");
        settler.clearPayer();
    }

    /// @notice Test that msgSender() fails with zero payer
    /// @dev When _msgSender() returns zero, the function should revert
    function test_msgSender_FailsWithZeroPayer() public {
        settler.clearPayer();
        vm.expectRevert();
        settler.msgSender();
    }

    /// @notice Test that msgSender() returns different payers correctly
    function test_msgSender_ReturnsDifferentPayers() public {
        address payer1 = makeAddr("payer1");
        address payer2 = makeAddr("payer2");

        // Set first payer
        settler.setPayer(payer1);
        assertEq(settler.msgSender(), payer1, "should return payer1");

        // Change to second payer
        settler.setPayer(payer2);
        assertEq(settler.msgSender(), payer2, "should return payer2");

        settler.clearPayer();
    }

    /// @notice Test msgSender with a specific well-known address
    function test_msgSender_WithSpecificAddress() public {
        address specificAddr = 0x352650Ac2653508d946c4912B07895B22edd84CD;

        settler.setPayer(specificAddr);
        assertEq(settler.msgSender(), specificAddr, "msgSender should return the specific address");

        settler.clearPayer();
    }
}

/// @title MsgSender Stub Contract
/// @notice A minimal stub that implements the msgSender() logic from BaseMixin._fallback()
/// @dev Returns the payer from transient storage only if it's non-zero
contract MsgSenderStub is IMsgSender {
    /// @dev The _PAYER_SLOT from TransientStorage (Permit2Payment.sol:45)
    bytes32 private constant _PAYER_SLOT = 0x0000000000000000000000000000000000000000cd1e9517bb0cb8d0d5cde893;

    /// @notice Implementation of msgSender() from BaseMixin._fallback()
    /// @dev Returns _msgSender() only if the lock is held (payer is non-zero)
    function msgSender() external view override returns (address result) {
        result = _msgSender();
        require(result != address(0));
    }

    /// @dev Reads the payer from transient storage (replicates TransientStorage.getPayer())
    function _msgSender() internal view returns (address payer) {
        assembly ("memory-safe") {
            payer := tload(_PAYER_SLOT)
        }
    }

    /// @dev Test helper to set the payer in transient storage
    function setPayer(address payer) external {
        assembly ("memory-safe") {
            tstore(_PAYER_SLOT, payer)
        }
    }

    /// @dev Test helper to clear the payer from transient storage
    function clearPayer() external {
        assembly ("memory-safe") {
            tstore(_PAYER_SLOT, 0)
        }
    }
}

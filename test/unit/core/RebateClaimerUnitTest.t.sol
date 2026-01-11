// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "@forge-std/Test.sol";

/// @dev Interface for the rebateClaimer() external function (from src/core/UniswapV4.sol)
interface IRebateClaimer {
    function rebateClaimer() external view returns (address);
}

/// @title RebateClaimer Unit Tests
/// @notice Unit tests for the rebateClaimer() function on Base Settler
/// @dev rebateClaimer() is implemented via UniswapV4._fallback() and always returns a constant address
contract RebateClaimerUnitTest is Test {
    /// @dev The _PAYER_SLOT from TransientStorage (Permit2Payment.sol:45)
    bytes32 private constant _PAYER_SLOT = 0x0000000000000000000000000000000000000000cd1e9517bb0cb8d0d5cde893;

    /// @dev The expected rebateClaimer address (hardcoded in UniswapV4.sol:405)
    address private constant EXPECTED_REBATE_CLAIMER = 0x352650Ac2653508d946c4912B07895B22edd84CD;

    RebateClaimerStub internal settler;

    function setUp() public {
        settler = new RebateClaimerStub();
    }

    /// @notice Test that rebateClaimer() always returns the expected constant address
    function test_rebateClaimer_ReturnsConstantAddress() public view {
        address claimer = settler.rebateClaimer();
        assertEq(claimer, EXPECTED_REBATE_CLAIMER, "rebateClaimer should return the constant address");
    }

    /// @notice Test that rebateClaimer() returns the same address regardless of payer state
    function test_rebateClaimer_ReturnsConstantAddress_WithPayerSet() public {
        address testPayer = makeAddr("testPayer");

        // Set the payer in transient storage
        settler.setPayer(testPayer);

        // rebateClaimer should still return the constant address
        address claimer = settler.rebateClaimer();
        assertEq(
            claimer, EXPECTED_REBATE_CLAIMER, "rebateClaimer should return the constant address even with payer set"
        );

        // Cleanup
        settler.clearPayer();
    }

    /// @notice Fuzz test that rebateClaimer() always returns the constant address
    function testFuzz_rebateClaimer_AlwaysReturnsConstant(address randomPayer) public {
        vm.assume(randomPayer != address(0));

        settler.setPayer(randomPayer);
        address claimer = settler.rebateClaimer();
        assertEq(claimer, EXPECTED_REBATE_CLAIMER, "rebateClaimer should always return the constant address");
        settler.clearPayer();
    }

    /// @notice Test that rebateClaimer() works when called multiple times
    function test_rebateClaimer_ConsistentAcrossMultipleCalls() public view {
        address first = settler.rebateClaimer();
        address second = settler.rebateClaimer();
        address third = settler.rebateClaimer();

        assertEq(first, EXPECTED_REBATE_CLAIMER);
        assertEq(second, EXPECTED_REBATE_CLAIMER);
        assertEq(third, EXPECTED_REBATE_CLAIMER);
    }
}

/// @title RebateClaimer Stub Contract
/// @notice A minimal stub that implements the rebateClaimer() logic from UniswapV4._fallback()
/// @dev Always returns the constant address 0x352650Ac2653508d946c4912B07895B22edd84CD
contract RebateClaimerStub is IRebateClaimer {
    /// @dev The _PAYER_SLOT from TransientStorage (Permit2Payment.sol:45)
    bytes32 private constant _PAYER_SLOT = 0x0000000000000000000000000000000000000000cd1e9517bb0cb8d0d5cde893;

    /// @dev The expected rebateClaimer address (hardcoded in UniswapV4.sol:405)
    address private constant EXPECTED_REBATE_CLAIMER = 0x352650Ac2653508d946c4912B07895B22edd84CD;

    /// @notice Implementation of rebateClaimer() from UniswapV4._fallback()
    /// @dev Always returns the constant address
    function rebateClaimer() external pure override returns (address) {
        return EXPECTED_REBATE_CLAIMER;
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

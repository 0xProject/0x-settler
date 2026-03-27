// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "@forge-std/Test.sol";
import {uint512, alloc, Lib512MathAccessors, Lib512MathArithmetic} from "../../src/utils/512Math.sol";

/// @dev Differential fuzz test for lnQ256 against a Python/mpmath oracle.
/// Requires: python3 with mpmath installed.
/// Run: forge test --match-contract LnQ256FuzzTest --ffi
contract LnQ256FuzzTest is Test {
    using Lib512MathAccessors for uint512;
    using Lib512MathArithmetic for uint512;

    string private constant _SCRIPT = "test/0.8.25/lnq256_ffi.py";

    function _oracle(uint256 x_hi, uint256 x_lo) internal returns (uint256 r_hi, uint256 r_lo) {
        string[] memory args = new string[](4);
        args[0] = "python3";
        args[1] = _SCRIPT;
        args[2] = vm.toString(bytes32(x_hi));
        args[3] = vm.toString(bytes32(x_lo));
        bytes memory result = vm.ffi(args);
        (r_hi, r_lo) = abi.decode(result, (uint256, uint256));
    }

    function _lnQ256(uint256 x_hi, uint256 x_lo) internal pure returns (uint256 r_hi, uint256 r_lo) {
        uint512 x = alloc().from(x_hi, x_lo);
        uint512 r = x.lnQ256();
        return r.into();
    }

    // -- Regression: fallback path off-by-one (small input) --

    function test_lnQ256_fallback_small() public pure {
        // x = 5470252322849727863 — hits fallback (e=62, j=2), truth is q_hi
        (uint256 hi, uint256 lo) = _lnQ256(0, 5470252322849727863);
        assertEq(hi, 43, "fallback_small hi");
        assertEq(lo, 16889019340470071853067439075881865123112007607344987529412165292835758334132, "fallback_small lo");
    }

    // -- Regression: fallback path off-by-one (large input) --

    function test_lnQ256_fallback_large() public pure {
        (uint256 hi, uint256 lo) = _lnQ256(
            49590002482518600722096235393477546969822675130338127964506757832273491752091,
            97807460451165354233258765217849731639227940254759164340075517639864536386448
        );
        assertEq(hi, 354, "fallback_large hi");
        assertEq(lo, 5019523204623679558388365391451672011441830568049161463743068853284332192200, "fallback_large lo");
    }

    // -- Differential fuzz --

    function testFuzz_lnQ256_diff(uint256 x_hi, uint256 x_lo) external {
        if (x_hi == 0 && x_lo == 0) x_lo = 1;

        (uint256 expected_hi, uint256 expected_lo) = _oracle(x_hi, x_lo);
        (uint256 actual_hi, uint256 actual_lo) = _lnQ256(x_hi, x_lo);

        assertEq(actual_hi, expected_hi, "lnQ256 hi mismatch");
        assertEq(actual_lo, expected_lo, "lnQ256 lo mismatch");
    }
}

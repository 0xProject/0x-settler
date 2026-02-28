// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {SlowMath} from "../SlowMath.sol";
import {Test} from "@forge-std/Test.sol";

/// @dev Fuzz-tests the generated Lean model of 512Math._sqrt against
/// the same correctness properties used in 512Math.t.sol. Calls the
/// compiled Lean evaluator via `vm.ffi`.
///
/// Requires the `sqrt512-model` binary to be pre-built:
///   cd formal/sqrt/Sqrt512Proof && lake build sqrt512-model
contract Sqrt512ModelTest is Test {
    string private constant _BIN = "formal/sqrt/Sqrt512Proof/.lake/build/bin/sqrt512-model";

    function _sqrt512(uint256 x_hi, uint256 x_lo) internal returns (uint256) {
        string[] memory args = new string[](4);
        args[0] = _BIN;
        args[1] = "sqrt512";
        args[2] = vm.toString(bytes32(x_hi));
        args[3] = vm.toString(bytes32(x_lo));
        bytes memory result = vm.ffi(args);
        return abi.decode(result, (uint256));
    }

    function testSqrt512Model(uint256 x_hi, uint256 x_lo) external {
        // _sqrt assumes x_hi != 0 (the public sqrt dispatches to 256-bit sqrt otherwise)
        vm.assume(x_hi != 0);

        uint256 r = _sqrt512(x_hi, x_lo);

        // r^2 <= x
        (uint256 r2_lo, uint256 r2_hi) = SlowMath.fullMul(r, r);
        assertTrue((r2_hi < x_hi) || (r2_hi == x_hi && r2_lo <= x_lo), "sqrt too high");

        // (r+1)^2 > x  (unless r == max uint256)
        if (r == type(uint256).max) {
            assertTrue(
                x_hi > 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe
                    || (x_hi == 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe && x_lo != 0),
                "sqrt too low (overflow)"
            );
        } else {
            uint256 r1 = r + 1;
            (r2_lo, r2_hi) = SlowMath.fullMul(r1, r1);
            assertTrue((r2_hi > x_hi) || (r2_hi == x_hi && r2_lo > x_lo), "sqrt too low");
        }
    }
}

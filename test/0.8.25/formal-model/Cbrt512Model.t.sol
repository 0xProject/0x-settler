// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {SlowMath} from "../SlowMath.sol";
import {Test} from "@forge-std/Test.sol";

/// @dev Fuzz-tests the generated Lean models of 512Math.cbrt and
/// 512Math.cbrtUp against correctness properties: r³ ≤ x < (r+1)³ for floor,
/// (r-1)³ < x ≤ r³ for ceiling.
///
/// Requires the `cbrt512-model` binary to be pre-built:
///   cd formal/cbrt/Cbrt512Proof && lake build cbrt512-model
contract Cbrt512ModelTest is Test {
    string private constant _BIN = "formal/cbrt/Cbrt512Proof/.lake/build/bin/cbrt512-model";

    // -- helpers ----------------------------------------------------------

    function _ffi1(string memory fn, uint256 x_hi, uint256 x_lo) internal returns (uint256) {
        string[] memory args = new string[](4);
        args[0] = _BIN;
        args[1] = fn;
        args[2] = vm.toString(bytes32(x_hi));
        args[3] = vm.toString(bytes32(x_lo));
        bytes memory result = vm.ffi(args);
        return abi.decode(result, (uint256));
    }

    /// @dev 512-bit comparison: (a_hi, a_lo) > (b_hi, b_lo)
    function _gt512(uint256 aH, uint256 aL, uint256 bH, uint256 bL) internal pure returns (bool) {
        return aH > bH || (aH == bH && aL > bL);
    }

    /// @dev 512-bit comparison: (a_hi, a_lo) >= (b_hi, b_lo)
    function _ge512(uint256 aH, uint256 aL, uint256 bH, uint256 bL) internal pure returns (bool) {
        return aH > bH || (aH == bH && aL >= bL);
    }

    /// @dev Multiply a 512-bit value (a_hi, a_lo) by a 256-bit value b, returning
    ///      a 512-bit result (truncated to 512 bits, sufficient for cube root checks).
    ///      r³ fits in 512 bits when r < 2^171.
    function _mul512x256(uint256 aH, uint256 aL, uint256 b) internal pure returns (uint256 rH, uint256 rL) {
        // Low part: aL * b (512-bit product)
        (rL, rH) = SlowMath.fullMul(aL, b);
        // High part: aH * b (only low 256 bits contribute since we truncate to 512 bits)
        unchecked {
            rH += aH * b;
        }
    }

    // -- floor cbrt: model_cbrt512_evm (x_hi > 0) --------------------------

    function testCbrt512Model(uint256 x_hi, uint256 x_lo) external {
        // _cbrt assumes x_hi != 0 (the public cbrt dispatches to 256-bit cbrt otherwise)
        vm.assume(x_hi != 0);

        uint256 r = _ffi1("cbrt512", x_hi, x_lo);

        // r³ ≤ x: compute r² then r³
        (uint256 r2_lo, uint256 r2_hi) = SlowMath.fullMul(r, r);
        (uint256 r3_hi, uint256 r3_lo) = _mul512x256(r2_hi, r2_lo, r);
        assertTrue(!_gt512(r3_hi, r3_lo, x_hi, x_lo), "cbrt too high: r^3 > x");

        // (r+1)³ > x
        if (r < type(uint256).max) {
            uint256 r1 = r + 1;
            (r2_lo, r2_hi) = SlowMath.fullMul(r1, r1);
            (r3_hi, r3_lo) = _mul512x256(r2_hi, r2_lo, r1);
            assertTrue(_gt512(r3_hi, r3_lo, x_hi, x_lo), "cbrt too low: (r+1)^3 <= x");
        }
    }

    // -- floor cbrt: model_cbrt512_wrapper_evm (full range) -----------------

    function testCbrt512WrapperModel(uint256 x_hi, uint256 x_lo) external {
        uint256 r = _ffi1("cbrt512_wrapper", x_hi, x_lo);

        // r³ ≤ x
        (uint256 r2_lo, uint256 r2_hi) = SlowMath.fullMul(r, r);
        (uint256 r3_hi, uint256 r3_lo) = _mul512x256(r2_hi, r2_lo, r);
        assertTrue(!_gt512(r3_hi, r3_lo, x_hi, x_lo), "wrapper cbrt too high: r^3 > x");

        // (r+1)³ > x
        if (r < type(uint256).max) {
            uint256 r1 = r + 1;
            (r2_lo, r2_hi) = SlowMath.fullMul(r1, r1);
            (r3_hi, r3_lo) = _mul512x256(r2_hi, r2_lo, r1);
            assertTrue(_gt512(r3_hi, r3_lo, x_hi, x_lo), "wrapper cbrt too low: (r+1)^3 <= x");
        }
    }

    // -- ceiling cbrt: model_cbrtUp512_wrapper_evm --------------------------

    function testCbrtUp512Model(uint256 x_hi, uint256 x_lo) external {
        uint256 r = _ffi1("cbrtUp512_wrapper", x_hi, x_lo);

        // x ≤ r³
        (uint256 r2_lo, uint256 r2_hi) = SlowMath.fullMul(r, r);
        (uint256 r3_hi, uint256 r3_lo) = _mul512x256(r2_hi, r2_lo, r);
        assertTrue(_ge512(r3_hi, r3_lo, x_hi, x_lo), "cbrtUp too low: r^3 < x");

        // (r-1)³ < x (r is minimal)
        if (r > 0) {
            uint256 rm = r - 1;
            (r2_lo, r2_hi) = SlowMath.fullMul(rm, rm);
            (r3_hi, r3_lo) = _mul512x256(r2_hi, r2_lo, rm);
            assertTrue(!_ge512(r3_hi, r3_lo, x_hi, x_lo), "cbrtUp too high: (r-1)^3 >= x");
        } else {
            // r = 0, x must be 0
            assertEq(x_hi, 0, "cbrtUp r=0 but x_hi!=0");
            assertEq(x_lo, 0, "cbrtUp r=0 but x_lo!=0");
        }
    }
}

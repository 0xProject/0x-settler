// SPDX-License-Identifier: MIT
pragma solidity ^0.8.34;

import {Exp} from "src/vendor/Exp.sol";
import {Ln} from "src/vendor/Ln.sol";
import {Test, stdError} from "@forge-std/Test.sol";

contract ExpTest is Test {
    // First input whose octave count exceeds the supported range; `expRayToWad` reverts here.
    int256 private constant _TOO_BIG = 0x8e383a2cdfa1b74a9422d2e1;
    // floor(1e27 * ln(1e-18)): the greatest input whose exact result is < 1 and floors to 0.
    int256 private constant _ZERO_MAX = -41446531673892822312323846185;
    // Central octave in ray input: [floor(-1e27 * ln(2) / 2), ceil(1e27 * ln(2) / 2)).
    int256 private constant _CENTRAL_X_LO = -346573590279972654708616061;
    int256 private constant _CENTRAL_X_HI = 346573590279972654708616061;
    // Central octave [1/sqrt(2), sqrt(2)) in wad: the image over which the round trip is exact.
    uint256 private constant _W_LO = 707106781186547525;
    uint256 private constant _W_HI = 1414213562373095048;

    /// High-precision oracle: floor(1e18 * exp(x / 1e27)) via 120-digit arithmetic.
    function _ref(int256 x) internal returns (int256) {
        string[] memory cmd = new string[](3);
        cmd[0] = "python3";
        cmd[1] = "test/0.8.34/exp_ref.py";
        cmd[2] = vm.toString(x);
        return abi.decode(vm.ffi(cmd), (int256));
    }

    function expRayToWadExternal(int256 x) external pure returns (int256) {
        return Exp.expRayToWad(x);
    }

    /// Differential fuzz against the oracle: never overestimates and is floor-or-one-less across
    /// the whole supported range. FFI spawns a process per run, so the run count is reduced.
    /// forge-config: default.fuzz.runs = 512
    function testFuzzExpRayToWadDifferential(int256 x) external {
        x = bound(x, _ZERO_MAX, _TOO_BIG - 1);
        int256 r = Exp.expRayToWad(x);
        int256 ref = _ref(x);
        assertLe(r, ref, "overestimates exp");
        assertGe(r, ref - 1, "below floor minus one");
        assertGe(r, int256(0), "negative result");
    }

    function testExpRayToWadExactZero() external pure {
        assertEq(Exp.expRayToWad(0), 1e18, "expRayToWad(0) != 1e18");
    }

    /// Direct oracle check over the central reduced-argument band, where the output is exact.
    /// FFI spawns a process per run, so the run count is reduced.
    /// forge-config: default.fuzz.runs = 512
    function testFuzzExpRayToWadCentralExact(int256 x) external {
        x = bound(x, _CENTRAL_X_LO, _CENTRAL_X_HI - 1);
        assertEq(Exp.expRayToWad(x), _ref(x), "central floor not exact");
    }

    function testExpRayToWadOverRangeReverts() external {
        vm.expectRevert(stdError.arithmeticError);
        this.expRayToWadExternal(_TOO_BIG);
        vm.expectRevert(stdError.arithmeticError);
        this.expRayToWadExternal(type(int256).max);
    }

    function testExpRayToWadUnderflowZero() external pure {
        assertEq(Exp.expRayToWad(_ZERO_MAX), 0, "boundary not zero");
        assertEq(Exp.expRayToWad(_ZERO_MAX - 1), 0, "below boundary not zero");
        assertEq(Exp.expRayToWad(-50e27), 0, "deep negative not zero");
        assertEq(Exp.expRayToWad(-1e40), 0, "reduction-overflow region not zero");
        assertEq(Exp.expRayToWad(type(int256).min), 0, "int256.min not zero");
    }

    /// Round trip against `Ln` on the central octave: exactly off-by-one, and exact at the scale
    /// point. A consumer in this regime recovers `w` by adding one.
    function testFuzzExpRayToWadRoundTrip(uint256 w) external pure {
        w = bound(w, _W_LO, _W_HI);
        int256 back = Exp.expRayToWad(Ln.lnWadToRay(int256(w)));
        if (w == 1e18) {
            assertEq(back, int256(w), "scale point not exact");
        } else {
            assertEq(back, int256(w) - 1, "round trip not w-1");
        }
    }

    function testExpRayToWadRoundTripBoundaries() external pure {
        assertEq(Exp.expRayToWad(Ln.lnWadToRay(int256(_W_LO))), int256(_W_LO) - 1);
        assertEq(Exp.expRayToWad(Ln.lnWadToRay(int256(_W_HI))), int256(_W_HI) - 1);
        assertEq(Exp.expRayToWad(Ln.lnWadToRay(1e18)), 1e18);
        assertEq(Exp.expRayToWad(Ln.lnWadToRay(1e18 + 1)), 1e18); // w-1
        assertEq(Exp.expRayToWad(Ln.lnWadToRay(1e18 - 1)), 1e18 - 2); // w-1
    }

    function testFuzzExpRayToWadMonotone(int256 x) external pure {
        x = bound(x, _ZERO_MAX, _TOO_BIG - 2);
        assertGe(Exp.expRayToWad(x + 1), Exp.expRayToWad(x), "not monotone");
    }
}

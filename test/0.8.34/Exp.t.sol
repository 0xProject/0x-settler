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
    // Canonical central wad inputs satisfying 1/sqrt(2) <= w/1e18 < sqrt(2).
    uint256 private constant _W_LO = 707106781186547525;
    uint256 private constant _W_HI = 1414213562373095048;

    function expRayToWadExternal(int256 x) external pure returns (int256) {
        return Exp.expRayToWad(x);
    }

    function testExpRayToWadExactZero() external pure {
        assertEq(Exp.expRayToWad(0), 1e18, "expRayToWad(0) != 1e18");
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
    function testExpRayToWadRoundTripBoundaries() external pure {
        assertEq(Exp.expRayToWad(Ln.lnWadToRay(int256(_W_LO))), int256(_W_LO) - 1);
        assertEq(Exp.expRayToWad(Ln.lnWadToRay(int256(_W_HI))), int256(_W_HI) - 1);
        assertEq(Exp.expRayToWad(Ln.lnWadToRay(1e18)), 1e18);
        assertEq(Exp.expRayToWad(Ln.lnWadToRay(1e18 + 1)), 1e18); // w-1
        assertEq(Exp.expRayToWad(Ln.lnWadToRay(1e18 - 1)), 1e18 - 2); // w-1
    }

    /// First input of octave k: the least x with round(x / (10**27 * ln2)) == k, computed as
    /// ceil((k*2**200 - 2**199) / CINV) with CINV = round(2**200 / (10**27 * ln2)), the same
    /// reciprocal the kernel rounds with.
    function _octaveStart(int256 k) private pure returns (int256) {
        int256 CINV = 0x724d54edbacbebbb95c52a0f6076;
        int256 num = k * (int256(1) << 200) - (int256(1) << 199);
        return num >= 0 ? (num + CINV - 1) / CINV : num / CINV;
    }

    /// Monotonicity is tightest where the octave count increments and the margin doubles. Check
    /// every octave boundary in the supported range deterministically.
    function testExpRayToWadOctaveBoundaryMonotone() external pure {
        for (int256 k = -60; k <= 63; ++k) {
            int256 xb = _octaveStart(k);
            for (int256 x = xb - 2; x <= xb + 1; ++x) {
                if (x + 1 >= _TOO_BIG) continue;
                assertGe(Exp.expRayToWad(x + 1), Exp.expRayToWad(x), "octave-boundary monotonicity");
            }
        }
    }

    /// High-k inputs whose exact result sits just below an integer: the tightest points for the
    /// never-overestimate guarantee, where the over-side envelope (rational approximation plus the
    /// Horner/sdiv truncation jitter) the margin must cover is largest, scaling as 2ᵏ.
    function testExpRayToWadNeverOverestimateHighK() external pure {
        int256[4] memory xs = [
            int256(44014845965556527147989858478),
            43997357674525079384913362454,
            43314167405007111804561657812,
            43956299042314536509785490661
        ];
        int256[4] memory floors = [
            int256(13043817825332782212292423780355560294),
            12817686828684532031135154053443771706,
            6472974441739539356346729565753819877,
            12302067878139647644374925801327210534
        ];
        for (uint256 i; i < xs.length; ++i) {
            int256 r = Exp.expRayToWad(xs[i]);
            assertLe(r, floors[i], "overestimates exp");
            assertGe(r, floors[i] - 1, "below floor minus one");
        }
    }
}

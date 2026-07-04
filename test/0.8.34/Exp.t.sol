// SPDX-License-Identifier: MIT
pragma solidity ^0.8.34;

import {Exp} from "src/vendor/Exp.sol";
import {Ln} from "src/vendor/Ln.sol";
import {Test, stdError} from "@forge-std/Test.sol";

contract ExpTest is Test {
    // First input whose octave count exceeds the supported range; `expRayToWad` reverts here.
    int256 private constant _TOO_BIG = 0x907595ccd30708cabec8a9db;
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

    /// The +1 pin at x = 0 sits between its neighbors: E(-1) and E(1) straddle 10**18 by ~1e-9
    /// ulp, far above the accumulator deficit, so both neighbors floor exactly and bracket the
    /// pinned value.
    function testExpRayToWadScalePointNeighbors() external pure {
        assertEq(Exp.expRayToWad(-1), 1e18 - 1, "expRayToWad(-1) != 1e18 - 1");
        assertEq(Exp.expRayToWad(1), 1e18, "expRayToWad(1) != 1e18");
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
        // First input past the clamp: E - 1 ~= 3.2e-28, so floor(E) = 1.
        assertEq(Exp.expRayToWad(_ZERO_MAX + 1), 1, "first live input not one");
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

    /// The round trip at fuzzed points of the central octave: `w - 1` everywhere except the exact
    /// scale point.
    function testFuzzExpRayToWadRoundTripCentral(uint256 w) external pure {
        w = bound(w, _W_LO, _W_HI);
        int256 expected = w == 1e18 ? int256(w) : int256(w) - 1;
        assertEq(Exp.expRayToWad(Ln.lnWadToRay(int256(w))), expected, "central round trip");
    }

    /// First input of octave k: the least x with round(x / (10**27 * ln2)) == k, computed as
    /// ceil((k*2**192 - 2**191) / CINV) with CINV = round(2**192 / (10**27 * ln2)), the same
    /// reciprocal the kernel rounds with.
    function _octaveStart(int256 k) private pure returns (int256) {
        int256 CINV = 0x724d54edbacbebbb95c52a0f60;
        int256 num = k * (int256(1) << 192) - (int256(1) << 191);
        return num >= 0 ? (num + CINV - 1) / CINV : num / CINV;
    }

    /// Monotonicity is tightest where the octave count increments and the margin doubles. Check
    /// every octave boundary in the supported range deterministically.
    function testExpRayToWadOctaveBoundaryMonotone() external pure {
        for (int256 k = -60; k <= 65; ++k) {
            int256 xb = _octaveStart(k);
            for (int256 x = xb - 2; x <= xb + 1; ++x) {
                if (x + 1 >= _TOO_BIG) continue;
                assertGe(Exp.expRayToWad(x + 1), Exp.expRayToWad(x), "octave-boundary monotonicity");
            }
        }
    }

    /// High-k inputs whose exact result sits just below an integer: the tightest points for the
    /// never-overestimate guarantee, where the over-side envelope (rational approximation plus the
    /// Horner truncation jitter) the margin must cover is largest, scaling as 2ᵏ.
    function testExpRayToWadNeverOverestimateHighK() external pure {
        int256[7] memory xs = [
            int256(44014845965556527147989858478),
            43997357674525079384913362454,
            43314167405007111804561657812,
            43956299042314536509785490661,
            44585114869649660801412478168,
            44194124950069992127775717862,
            44183539459288389725181420565
        ];
        int256[7] memory floors = [
            int256(13043817825332782212292423780355560294),
            12817686828684532031135154053443771706,
            6472974441739539356346729565753819877,
            12302067878139647644374925801327210534,
            23071156379767734423570518961257410973,
            15605029656619514838244041715971750817,
            15440713974442839033966209577600907121
        ];
        for (uint256 i; i < xs.length; ++i) {
            int256 r = Exp.expRayToWad(xs[i]);
            assertLe(r, floors[i], "overestimates exp");
            assertGe(r, floors[i] - 1, "below floor minus one");
        }
    }

    /// Exact value witnesses across the negative octaves, k = -1 down to k = -60 (the deepest
    /// octave above the clamp). Every point has
    /// frac(E) > 0.09 while the deficit envelope at k <= -1 is below 1e-19 ulp, so each result
    /// is exactly floor(E).
    function testExpRayToWadNegativeHalfExactFloor() external pure {
        int256[8] memory xs = [
            int256(-1e27), // k = -1
            -1.5e27, // k = -2
            -5e27, // k = -7
            -10e27, // k = -14
            -20e27, // k = -29
            -30e27, // k = -43
            -40e27, // k = -58
            -41.3e27 // k = -60
        ];
        int256[8] memory floors =
            [int256(367879441171442321), 223130160148429828, 6737946999085467, 45399929762484, 2061153622, 93576, 4, 1];
        for (uint256 i; i < xs.length; ++i) {
            assertEq(Exp.expRayToWad(xs[i]), floors[i], "negative-half floor");
        }
    }

    /// The largest supported input, one below the revert threshold: frac(E) ~= 0.52 sits inside
    /// the k = 64 deficit envelope (~0.70), so the result floors to E or one under. At the top of
    /// k = 63, frac(E) ~= 0.74 exceeds that octave's envelope (~0.35) and the floor is exact.
    function testExpRayToWadSupportedEdge() external pure {
        int256 floorE = 26087635650665564424699143611138320962;
        int256 r = Exp.expRayToWad(_TOO_BIG - 1);
        assertLe(r, floorE, "overestimates exp");
        assertGe(r, floorE - 1, "below floor minus one");
        assertEq(
            Exp.expRayToWad(44014845965556527147994239712),
            13043817825332782212349571798501714341,
            "k = 63 top floor"
        );
    }

    /// The 1-ulp underestimate is achieved: the least x >= 44e27 whose result is floor(E) - 1.
    /// frac(E) ~= 0.1605 sits below the accumulated deficit at k = 63, so the floored accumulator
    /// lands one under the exact floor.
    function testExpRayToWadUnderestimateByOneWitness() external pure {
        int256 x = 44000000000000000000000000001;
        int256 floorE = 12851600114359308275809299644994699372;
        assertEq(Exp.expRayToWad(x), floorE - 1, "not the 1-ulp underestimate");
        // The first input of the k = 64 octave: frac(E) ~= 0.07, again one under the exact floor.
        assertEq(
            Exp.expRayToWad(44014845965556527147994239713),
            13043817825332782212349571811545532167 - 1,
            "k = 64 underestimate"
        );
    }

    /// Never negative and monotone at every adjacent pair; oracle-free, so it covers octave
    /// interiors and the clamp seam without an external reference.
    function testFuzzExpRayToWadMonotoneNonNegative(int256 x) external pure {
        x = bound(x, _ZERO_MAX - 1e27, _TOO_BIG - 2);
        int256 r = Exp.expRayToWad(x);
        assertGe(r, 0, "negative result");
        assertGe(Exp.expRayToWad(x + 1), r, "adjacent monotonicity");
    }
}

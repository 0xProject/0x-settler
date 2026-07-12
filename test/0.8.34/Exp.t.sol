// SPDX-License-Identifier: MIT
pragma solidity ^0.8.34;

import {Exp} from "src/vendor/Exp.sol";
import {Ln} from "src/vendor/Ln.sol";
import {Clz} from "src/vendor/Clz.sol";
import {Test, stdError} from "@forge-std/Test.sol";

contract ExpTest is Test {
    // The largest magnitude admitted by `mulExpRay`'s s <= 127 guard.
    uint256 private constant _SCALE_MAX = 0x7fffffffffffffffffffffffffffffff;
    int128 private constant _Y_MAX = type(int128).max;
    // First input whose octave count exceeds the supported range; `expRayToWad` reverts here.
    int256 private constant _TOO_BIG = 0x92b2f16cc66c5a4ae96e80d4;
    // First input whose octave count reaches 125: the accuracy-guard boundary at the deepest
    // scale headroom reachable with a nonzero multiplier (abs(y) = 1, s = 126).
    int256 private constant _X_HI = 86296823979713191022445399122;
    // First input whose octave count reaches 126; `mulExpRay` reverts here for every y.
    int256 private constant _MUL_HI = 86989971160273136331862631244;
    // First input whose octave count reaches -127; all supported magnitudes floor to zero here.
    int256 private constant _X_LO_ZERO = -88376265521393026950697095485;
    // floor(1e27 * ln(1e-18)): the greatest input whose exact result is < 1 and floors to 0.
    int256 private constant _ZERO_MAX = -41446531673892822312323846185;
    // Canonical central wad inputs satisfying 1/sqrt(2) <= w/1e18 < sqrt(2).
    uint256 private constant _W_LO = 707106781186547525;
    uint256 private constant _W_HI = 1414213562373095048;

    function expRayToWadExternal(int256 x) external pure returns (int256) {
        return Exp.expRayToWad(x);
    }

    function mulExpRayExternal(int128 y, int256 x) external pure returns (int256) {
        return Exp.mulExpRay(y, x);
    }

    function mulExpRayDirtyY(uint256 dirtyY, int256 x) public pure returns (int256) {
        int128 y;
        // Solidity cannot construct a narrow signed value with dirty upper bits.
        // Equivalent value: y = int128(uint128(dirtyY)).
        assembly ("memory-safe") {
            y := dirtyY
        }
        return Exp.mulExpRay(y, x);
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
        for (int256 k = -60; k <= 66; ++k) {
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
        int256[8] memory xs = [
            int256(44014845965556527147989858478),
            43997357674525079384913362454,
            43314167405007111804561657812,
            43956299042314536509785490661,
            44585114869649660801412478168,
            44194124950069992127775717862,
            44183539459288389725181420565,
            44881638328706512051022125121
        ];
        int256[8] memory floors = [
            int256(13043817825332782212292423780355560294),
            12817686828684532031135154053443771706,
            6472974441739539356346729565753819877,
            12302067878139647644374925801327210534,
            23071156379767734423570518961257410973,
            15605029656619514838244041715971750817,
            15440713974442839033966209577600907121,
            31034722391555079924522474771845545397
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

    /// The largest supported input, one below the revert threshold: frac(E) ~= 0.79 sits inside
    /// the k = 65 deficit envelope (~1.0), so the result floors to E or one under. At the top of
    /// k = 64, frac(E) ~= 0.52 exceeds that octave's envelope (~0.50) and the floor is exact.
    function testExpRayToWadSupportedEdge() external pure {
        int256 floorE = 52175271301331128849398287198371155181;
        int256 r = Exp.expRayToWad(_TOO_BIG - 1);
        assertLe(r, floorE, "overestimates exp");
        assertGe(r, floorE - 1, "below floor minus one");
        assertEq(
            Exp.expRayToWad(44707993146116472457411471834), 26087635650665564424699143611138320962, "k = 64 top floor"
        );
    }

    /// The 1-ulp underestimate is achieved: k = 64 inputs whose frac(E) (~0.17 and ~0.07) sits
    /// below the accumulated deficit, so the floored accumulator lands one under the exact floor.
    function testExpRayToWadUnderestimateByOneWitness() external pure {
        int256 x = 44044505178945024895948687544;
        int256 floorE = 13436481464873958299464002666966885694;
        assertEq(Exp.expRayToWad(x), floorE - 1, "not the 1-ulp underestimate");
        // The first input of the k = 64 octave, again one under the exact floor.
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

    function testMulExpRaySpecializesExpRayToWad() external pure {
        int256[12] memory xs = [
            int256(_X_LO_ZERO),
            _X_LO_ZERO + 1,
            _ZERO_MAX,
            _ZERO_MAX + 1,
            -1,
            0,
            1,
            44014845965556527147989858478,
            44044505178945024895948687544,
            44707993146116472457411471834,
            _TOO_BIG - 1,
            -50e27
        ];
        for (uint256 i; i < xs.length; ++i) {
            assertEq(Exp.mulExpRay(1e18, xs[i]), Exp.expRayToWad(xs[i]), "wad specialization");
        }
    }

    /// x = 0 is pinned exactly wherever it is accepted: acceptance needs two bits of closing
    /// shift, i.e. 4*abs(y) <= _SCALE_MAX. One unit of magnitude past that boundary reverts.
    function testMulExpRayScalePoint() external {
        assertEq(Exp.mulExpRay(1, 0), 1, "one");
        assertEq(Exp.mulExpRay(-1, 0), -1, "minus one");
        int128 pinMax = _Y_MAX / 4;
        assertEq(Exp.mulExpRay(pinMax, 0), pinMax, "deepest pinned magnitude");
        assertEq(Exp.mulExpRay(-pinMax, 0), -pinMax, "negative mirror");
        vm.expectRevert(stdError.arithmeticError);
        this.mulExpRayExternal(pinMax + 1, 0);
        vm.expectRevert(stdError.arithmeticError);
        this.mulExpRayExternal(-(pinMax + 1), 0);
    }

    /// At abs(y) = _SCALE_MAX (s = 0), octave k = -2 is the highest accepted octave and the
    /// closing shift is exactly 2. The two-unit bracket must hold at both ends of that octave.
    function testMulExpRayScaleCapLive() external pure {
        int256 x = _octaveStart(-2);
        int256 floorA = 30076996146000563943129221579116071223;
        int256 r = Exp.mulExpRay(_Y_MAX, x);
        assertLe(r, floorA, "overestimates");
        assertGe(r, floorA - 1, "below floor minus one");
        assertEq(Exp.mulExpRay(-_Y_MAX, x), -r, "negative mirror");

        x = -1039720770839917964125848183;
        assertEq(x, _octaveStart(-1) - 1, "upper endpoint");
        floorA = 60153992292001127886258443070517000410;
        r = Exp.mulExpRay(_Y_MAX, x);
        assertLe(r, floorA, "overestimates at upper endpoint");
        assertGe(r, floorA - 1, "below floor minus one at upper endpoint");
        assertEq(Exp.mulExpRay(-_Y_MAX, x), -r, "negative mirror at upper endpoint");
    }

    /// Below the octave-wrap boundary (x < -(2**255 + 2**191)/CINV ~ -5.7e45) the wrapped octave
    /// word decides between revert and the zero clamp; either is within the bracket (A < 1 at
    /// every supported magnitude). One deterministic witness each way, plus the boundary pair.
    function testMulExpRayWrappedOctave() external {
        // 2**191 + CINV*x wraps to exactly zero: octave word 0, closing shift 67, clamps.
        assertEq(
            Exp.mulExpRay(1e18, -57402104550644550183762763389232637323199440519166886170539266728770553249792),
            0,
            "wrapped word 0 clamps"
        );
        assertEq(Exp.mulExpRay(1e18, type(int256).min), 0, "int256.min clamps");
        // The deepest wrap-free x: octave word -2**63, closing shift far above 2, clamps.
        assertEq(Exp.mulExpRay(1e18, -6393154322601327830240888940151524429370348050), 0, "deepest wrap-free x clamps");
        // One below it the product wraps positive (octave word 2**63 - 1) and the guard fires.
        vm.expectRevert(stdError.arithmeticError);
        this.mulExpRayExternal(1e18, -6393154322601327830240888940151524429370348051);
    }

    /// A zero multiplier takes the same guard as every other y: any x below the k = 126 fence is
    /// accepted (the maximal headroom s = 127 keeps the accuracy guard clear through k = 125) and
    /// returns zero; at or above the fence it reverts.
    function testMulExpRayZeroY() external {
        assertEq(Exp.mulExpRay(0, 0), 0, "zero x");
        assertEq(Exp.mulExpRay(0, type(int256).min), 0, "min x");
        assertEq(Exp.mulExpRay(0, _X_LO_ZERO), 0, "clamp boundary");
        assertEq(Exp.mulExpRay(0, _X_HI), 0, "octave 125 accepted only at zero magnitude");
        assertEq(Exp.mulExpRay(0, _MUL_HI - 1), 0, "greatest accepted x");
        vm.expectRevert(stdError.arithmeticError);
        this.mulExpRayExternal(0, _MUL_HI);
        vm.expectRevert(stdError.arithmeticError);
        this.mulExpRayExternal(0, type(int256).max);
    }

    /// `_SCALE_MAX_CLZ` inside the library must track the maximal sub-2**127 scale. The positive
    /// Q126 over envelope remains below one half, so its image at the cap is below one unit.
    function testScaleMaxClzPairing() external pure {
        assertEq(_SCALE_MAX, (uint256(1) << 127) - 1, "maximal 127-bit scale");
        assertLt(uint256(2 * 4668745981919039833), uint256(1e19), "over envelope below one half");
        assertEq(Clz.clz(_SCALE_MAX), 129, "_SCALE_MAX_CLZ");
        assertLe(uint256(1e18) << 67, _SCALE_MAX, "wad scale within the cap");
    }

    function testMulExpRayLowerZero() external pure {
        assertEq(Exp.mulExpRay(1, _X_LO_ZERO), 0, "one at boundary");
        assertEq(Exp.mulExpRay(_Y_MAX, _X_LO_ZERO), 0, "scale max at boundary");
        assertEq(Exp.mulExpRay(-_Y_MAX, _X_LO_ZERO - 1), 0, "negative below boundary");
    }

    function testMulExpRayNegativeSignSymmetry() external pure {
        int256 x = 3e27;
        int128 y = 123456789012345678901234567;
        assertEq(Exp.mulExpRay(-y, x), -Exp.mulExpRay(y, x), "positive exponent");
        assertEq(Exp.mulExpRay(-y, -x), -Exp.mulExpRay(y, -x), "negative exponent");
    }

    function testMulExpRayClearsDirtyYBits() external pure {
        uint256 positive = (type(uint256).max << 128) | uint256(uint128(1e18));
        uint256 negative = uint256(uint128(-int128(1e18)));
        assertEq(mulExpRayDirtyY(positive, 1e27), Exp.mulExpRay(1e18, 1e27), "dirty positive");
        assertEq(mulExpRayDirtyY(negative, 1e27), Exp.mulExpRay(-1e18, 1e27), "dirty negative");
    }

    function testMulExpRayMinReverts() external {
        vm.expectRevert(stdError.arithmeticError);
        this.mulExpRayExternal(type(int128).min, 0);
        vm.expectRevert(stdError.arithmeticError);
        this.mulExpRayExternal(type(int128).min, _X_LO_ZERO);
        vm.expectRevert(stdError.arithmeticError);
        this.mulExpRayExternal(type(int128).min, type(int256).min);
    }

    function testMulExpRayHighGuardReverts() external {
        // Octave 125 exceeds the headroom of any nonzero magnitude (accuracy guard) ...
        vm.expectRevert(stdError.arithmeticError);
        this.mulExpRayExternal(1, _X_HI);
        // ... and octave 126 is past the envelope for every y (unconditional fence).
        vm.expectRevert(stdError.arithmeticError);
        this.mulExpRayExternal(1, _MUL_HI);
        vm.expectRevert(stdError.arithmeticError);
        this.mulExpRayExternal(1, type(int256).max);
    }

    function testMulExpRayAccuracyGuardReverts() external {
        vm.expectRevert(stdError.arithmeticError);
        this.mulExpRayExternal(1e18, _TOO_BIG);
        vm.expectRevert(stdError.arithmeticError);
        this.mulExpRayExternal(_Y_MAX, _octaveStart(-1));
    }

    function testMulExpRaySmallMagnitudeHighOctave() external {
        assertGt(Exp.mulExpRay(1, _X_HI - 1), 0, "k = 124 accepted");
        vm.expectRevert(stdError.arithmeticError);
        this.mulExpRayExternal(1, _X_HI);
    }

    function testFuzzMulExpRaySpecializesExpRayToWad(int256 x) external pure {
        x = bound(x, _X_LO_ZERO - 1e27, _TOO_BIG - 1);
        assertEq(Exp.mulExpRay(1e18, x), Exp.expRayToWad(x), "wad specialization");
    }

    function testFuzzMulExpRaySignSymmetry(uint256 uy, int256 x) external pure {
        int128 y = int128(uint128(bound(uy, 1, 1e18)));
        x = bound(x, _X_LO_ZERO + 1, _TOO_BIG - 1);
        assertEq(Exp.mulExpRay(-y, x), -Exp.mulExpRay(y, x), "sign symmetry");
    }

    function testFuzzMulExpRayMonotoneMagnitude(uint256 uy, int256 x) external pure {
        int128 y = int128(uint128(bound(uy, 1, 1e18)));
        x = bound(x, _X_LO_ZERO + 1, _TOO_BIG - 2);
        assertGe(Exp.mulExpRay(y, x + 1), Exp.mulExpRay(y, x), "adjacent monotonicity");
    }

    /// Sweep every bit-length boundary, where a unit magnitude step lowers the headroom by one,
    /// at its deepest accepted octaves.
    function testMulExpRayMonotoneYHeadroomBoundaries() external pure {
        for (uint256 s0 = 1; s0 <= 126; ++s0) {
            int128 q = int128(uint128(_SCALE_MAX >> s0));
            int256 kmax = int256(s0) - 3;
            for (int256 k = kmax; k >= kmax - 2 && k >= -60; --k) {
                int256 xb = _octaveStart(k);
                for (int256 x = xb; x <= xb + 2; ++x) {
                    assertLe(Exp.mulExpRay(q, x), Exp.mulExpRay(q + 1, x), "y-monotonicity");
                    assertGe(Exp.mulExpRay(-q, x), Exp.mulExpRay(-(q + 1), x), "negative mirror");
                }
            }
        }
    }

    /// Fuzz the bit-length headroom boundaries across the full accepted exponent range.
    function testFuzzMulExpRayMonotoneYHeadroom(uint256 us, int256 x) external pure {
        uint256 s0 = bound(us, 1, 126);
        int128 q = int128(uint128(_SCALE_MAX >> s0));
        // The deepest x accepted by both magnitudes: octave count at most s0 - 3.
        x = bound(x, _X_LO_ZERO + 1, _octaveStart(int256(s0) - 2) - 1);
        assertLe(Exp.mulExpRay(q, x), Exp.mulExpRay(q + 1, x), "y-monotonicity across headroom");
        assertGe(Exp.mulExpRay(-q, x), Exp.mulExpRay(-(q + 1), x), "negative mirror");
    }

    /// Adjacent multipliers anywhere in the supported range, with the exponent bounded to the
    /// octaves both headrooms accept.
    function testFuzzMulExpRayMonotoneYAdjacent(uint256 uy, int256 x) external pure {
        int128 y = int128(uint128(bound(uy, 1, _SCALE_MAX - 1)));
        uint256 s = Clz.clz(uint256(uint128(y)) + 1) - 129;
        x = bound(x, _X_LO_ZERO + 1, _octaveStart(int256(s) - 1) - 1);
        assertLe(Exp.mulExpRay(y, x), Exp.mulExpRay(y + 1, x), "adjacent y-monotonicity");
    }
}

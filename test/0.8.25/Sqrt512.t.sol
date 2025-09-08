// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "lib/forge-std/src/Test.sol";

library Sqrt512Lib {
    function sqrt512(uint256 hi, uint256 lo) internal pure returns (uint256 root) {
        assembly {
            // ======================= 256x256 -> 512 (exact) =======================
            function mul512(a, b) -> rhi, rlo {
                rlo := mul(a, b)
                let mm := mulmod(a, b, not(0))
                rhi := sub(sub(mm, rlo), lt(mm, rlo))
            }

            function square512(x) -> rhi, rlo {
                rlo := mul(x, x)
                let mm := mulmod(x, x, not(0))
                rhi := sub(sub(mm, rlo), lt(mm, rlo))
            }

            // ======================= 512 -> 256 shifts (branch-light) =======================
            function shr512To256(ahi, alo, k) -> r {
                let a := or(shr(k, alo), shl(sub(256, k), ahi))
                let b := shr(sub(k, 256), ahi)
                r := or(a, b)
            }
            function shl512To256(ahi, alo, k) -> r { r := shl(k, alo) }

            // ======================= 512-bit add/sub/compare =======================
            function add512(ahi, alo, bhi, blo) -> rhi, rlo {
                rlo := add(alo, blo)
                rhi := add(add(ahi, bhi), lt(rlo, alo))
            }
            function sub512(ahi, alo, bhi, blo) -> rhi, rlo {
                rlo := sub(alo, blo)
                rhi := sub(sub(ahi, bhi), lt(alo, blo))
            }
            function lt512(ahi, alo, bhi, blo) -> r {
                r := or(lt(ahi, bhi), and(eq(ahi, bhi), lt(alo, blo)))
            }

            // ======================= Q1.255 multiplies (fast >>255) =======================
            // floor((a*b) / 2^255)
            function mulShrDown255(a, b) -> z {
                let rhi, rlo := mul512(a, b)
                // fast ((hi:lo)>>255)
                z := or(shr(255, rlo), shl(1, rhi))
            }
            // ceil((a*b) / 2^255)
            function mulShrUp255(a, b) -> z {
                let rhi, rlo := mul512(a, b)
                z := or(shr(255, rlo), shl(1, rhi))
                // add 1 if any of the low 255 bits are set
                z := add(z, iszero(iszero(and(rlo, 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff))))
            }
            // ceil(x/2)
            function half_up(x) -> y { y := shr(1, add(x, 1)) }

            // ======================= clz256 (branchless) =======================
            function clz256(x) -> r {
                r := shl(7, lt(0xffffffffffffffffffffffffffffffff, x))
                r := or(r, shl(6, lt(0xffffffffffffffff, shr(r, x))))
                r := or(r, shl(5, lt(0xffffffff,           shr(r, x))))
                r := or(r, shl(4, lt(0xffff,               shr(r, x))))
                r := or(r, shl(3, lt(0xff,                 shr(r, x))))
                r := add(
                    xor(
                        r,
                        byte(
                            and(0x1f, shr(shr(r, x), 0x8421084210842108cc6318c6db6d54be)),
                            0xf8f9f9faf9fdfafbf9fdfcfdfafbfcfef9fafdfafcfcfbfefafafcfbffffffff
                        )
                    ),
                    iszero(x)
                )
            }

            // ======================= Robust normalization: twoe & e =======================
            function compute_twoe(ahi, alo) -> twoe, e {
                if ahi {
                    twoe := and(sub(512, clz256(ahi)), not(1))
                }
                if iszero(ahi) {
                    twoe := and(sub(256, clz256(alo)), not(1))
                }
                e := shr(1, twoe)
            }

            // ======================= Robust under-biased rsqrt step =======================
            function rsqrt_step_under(M, Y, TH, inc) -> Yn {
                let Y2_up  := mulShrUp255(Y, Y)
                let MY2_up := mulShrUp255(M, Y2_up)
                let U := add(MY2_up, inc)
                let H_up := half_up(U)
                let T_down := sub(TH, H_up)
                Yn := mulShrDown255(Y, T_down)
            }

            // ======================= Main =======================
            function isqrt512(ahi, alo) -> r {
                if iszero(or(ahi, alo)) { r := 0 leave }

                // ---- Normalize: N = m * 2^(2e), m ∈ [1/2, 2)
                let twoe, e := compute_twoe(ahi, alo)

                // M = floor(m * 2^255) = floor( N * 2^(255 - twoe) )
                let M := or(
                    shl512To256(ahi, alo, sub(255, twoe)),
                    shr512To256(ahi, alo, sub(twoe, 255))
                )

                // Precompute: TH = 1.5 * 2^255; inc = 1 + [m<1] (msb of M is bit 255)
                let TH := add(shl(255, 1), shl(254, 1))
                let inc := add(1, iszero(shr(255, M)))

                // ---- 8-bucket LUT by thresholds (≤3 compares in chosen half)
                let Y
                if iszero(shr(255, M)) {
                    // lower half: m < 1
                    if lt(M, shl(252, 5)) {
                        Y := 0xa1e89b12424876d9b744b679ebd7ff75576022564e0005ab1197680f04a16a99  // 5/8
                    }
                    if and(iszero(lt(M, shl(252, 5))), lt(M, shl(253, 3))) {
                        Y := 0x93cd3a2c8198e2690c7c0f257d92be830c9d66eec69e17dd97b58cc2cf6c8cf6  // 3/4
                    }
                    if and(iszero(lt(M, shl(253, 3))), lt(M, shl(252, 7))) {
                        Y := 0x88d6772b01214e4aaacbdb3b4a878420c5c99fff16522f67d002ca332aaabf66  // 7/8
                    }
                    if iszero(or(lt(M, shl(252, 5)), or(lt(M, shl(253, 3)), lt(M, shl(252, 7))))) {
                        Y := 0x8000000000000000000000000000000000000000000000000000000000000000  // 1
                    }
                }
                if shr(255, M) {
                    // upper half: m >= 1
                    if lt(M, shl(253, 5)) {
                        Y := 0x727c9716ffb764d594a519c0252be9ae6d00dc9194a760ed9691c407204d6c3b  // 5/4
                    }
                    if and(iszero(lt(M, shl(253, 5))), lt(M, shl(254, 3))) {
                        Y := 0x6882f5c030b0f7f010b306bb5e1c76d14900b826fd3c1ea0517f3098179a8128  // 3/2
                    }
                    if and(iszero(lt(M, shl(254, 3))), lt(M, shl(253, 7))) {
                        Y := 0x60c2479a9fdf9a228b3c8e96d2c84dd553c7ffc87ee4c448a699ceb6a698da73  // 7/4
                    }
                    if iszero(or(lt(M, shl(253, 5)), or(lt(M, shl(254, 3)), lt(M, shl(253, 7))))) {
                        Y := 0x5a827999fcef32422cbec4d9baa55f4f8eb7b05d449dd426768bd642c199cc8a  // 2
                    }
                }

                // ---- Newton core (Q1.255): 5 base + up-to-2 gated
                Y := rsqrt_step_under(M, Y, TH, inc)
                Y := rsqrt_step_under(M, Y, TH, inc)
                Y := rsqrt_step_under(M, Y, TH, inc)
                Y := rsqrt_step_under(M, Y, TH, inc)
                Y := rsqrt_step_under(M, Y, TH, inc)
                if gt(e, 62) {
                    Y := rsqrt_step_under(M, Y, TH, inc)
                    if gt(e, 122) {
                        Y := rsqrt_step_under(M, Y, TH, inc)
                    }
                }

                // ---- Combine (lower bound): r0 = floor( (M * Y) / 2^(510 - e) )
                let pHi, pLo := mul512(M, Y)
                let r0 := shr512To256(pHi, pLo, sub(510, e))

                // ---- Δ = N - r0^2
                let r2hi, r2lo := square512(r0)
                let dHi, dLo := sub512(ahi, alo, r2hi, r2lo)

                // ---- Precompute 2r0, 4r0, 8r0 via shifts
                let SLo := shl(1, r0)
                let SHi := shr(255, r0)
                let S2Lo := shl(2, r0)
                let S2Hi := shr(254, r0)
                let S4Lo := shl(3, r0)
                let S4Hi := shr(253, r0)

                // ======================= HYBRID FIXUP (+0..+7) =======================
                // Split at τ4 = 8r0 + 16 (1 jump), then final add is branch-free per half.

                // τ4 = 8r0 + 16
                let t4Lo := add(S4Lo, 16)
                let t4Hi := add(S4Hi, lt(t4Lo, 16))

                if lt512(dHi, dLo, t4Hi, t4Lo) {
                    // ---- lower half: k ∈ {0,1,2,3}
                    // τ2 = 4r0 + 4
                    let t2Lo := add(S2Lo, 4)
                    let t2Hi := add(S2Hi, lt(t2Lo, 4))

                    if lt512(dHi, dLo, t2Hi, t2Lo) {
                        // k ∈ {0,1}. τ1 = 2r0 + 1  (SLo even ⇒ no carry)
                        let t1Lo := add(SLo, 1)
                        // b1 = (Δ >= τ1)
                        let b1 := xor( lt512(dHi, dLo, SHi, t1Lo), 1 )
                        r := add(r0, b1)
                        leave
                    }

                    // k ∈ {2,3}. τ3 = 6r0 + 9 = (4r0 + 2r0) + 9
                    let t3Lo := add(S2Lo, SLo)
                    let c3a := lt(t3Lo, S2Lo)
                    let t3Hi := add(add(S2Hi, SHi), c3a)
                    t3Lo := add(t3Lo, 9)
                    let c3b := lt(t3Lo, 9)
                    let t3Hi2 := add(t3Hi, c3b)

                    let b3 := xor( lt512(dHi, dLo, t3Hi2, t3Lo), 1 )
                    r := add(add(r0, 2), b3)
                    leave
                }

                // ---- upper half: k ∈ {4,5,6,7}
                // τ6 = 12r0 + 36 = (8r0 + 4r0) + 36
                let t6Lo := add(S4Lo, S2Lo)
                let c6a := lt(t6Lo, S4Lo)
                let t6Hi := add(add(S4Hi, S2Hi), c6a)
                t6Lo := add(t6Lo, 36)
                let c6b := lt(t6Lo, 36)
                let t6Hi2 := add(t6Hi, c6b)

                if lt512(dHi, dLo, t6Hi2, t6Lo) {
                    // k ∈ {4,5}. τ5 = 10r0 + 25 = (8r0 + 2r0) + 25
                    let t5Lo := add(S4Lo, SLo)
                    let c5a := lt(t5Lo, S4Lo)
                    let t5Hi := add(add(S4Hi, SHi), c5a)
                    t5Lo := add(t5Lo, 25)
                    let c5b := lt(t5Lo, 25)
                    let t5Hi2 := add(t5Hi, c5b)

                    let b5 := xor( lt512(dHi, dLo, t5Hi2, t5Lo), 1 )
                    r := add(add(r0, 4), b5)
                    leave
                }

                // k ∈ {6,7}. τ7 = 14r0 + 49 = (8r0 + 4r0 + 2r0) + 49
                {
                    let t7Lo := add(S4Lo, S2Lo)
                    let c7a := lt(t7Lo, S4Lo)
                    let t7Hi := add(add(add(S4Hi, S2Hi), SHi), c7a)
                    t7Lo := add(t7Lo, SLo)
                    let c7b := lt(t7Lo, SLo)
                    t7Hi := add(t7Hi, c7b)
                    t7Lo := add(t7Lo, 49)
                    let c7c := lt(t7Lo, 49)
                    t7Hi := add(t7Hi, c7c)

                    let b7 := xor( lt512(dHi, dLo, t7Hi, t7Lo), 1 )
                    r := add(add(r0, 6), b7)
                }
            }

            root := isqrt512(hi, lo)
        }
    }
}

contract Sqrt512Test is Test {
    // Comprehensive fuzz test
    function testFuzz_Sqrt512_Correctness(uint256 hi, uint256 lo) public pure {
        uint256 result = Sqrt512Lib.sqrt512(hi, lo);
        
        // Check: result^2 <= (hi:lo)
        (uint256 r2_hi, uint256 r2_lo) = mul512(result, result);
        bool resultSquaredFits = (r2_hi < hi) || (r2_hi == hi && r2_lo <= lo);
        assertTrue(resultSquaredFits, "result^2 should be <= input");
        
        // Check: (result+1)^2 > (hi:lo)
        // Special case: if result == 2^256-1, can't increment
        if (result < type(uint256).max) {
            uint256 resultPlus1 = result + 1;
            (uint256 r2p1_hi, uint256 r2p1_lo) = mul512(resultPlus1, resultPlus1);
            bool resultPlus1SquaredExceeds = (r2p1_hi > hi) || (r2p1_hi == hi && r2p1_lo > lo);
            assertTrue(resultPlus1SquaredExceeds, "(result+1)^2 should be > input");
        }
    }
    
    // Helper function for 256x256 multiplication
    function mul512(uint256 a, uint256 b) internal pure returns (uint256 hi, uint256 lo) {
        lo = a * b;
        uint256 mm = mulmod(a, b, type(uint256).max);
        hi = mm - lo;
        if (mm < lo) hi -= 1;
    }
    
    // Edge case tests
    function test_EdgeCases() public pure {
        // Test zero
        assertEq(Sqrt512Lib.sqrt512(0, 0), 0);
        
        // Test small values
        assertEq(Sqrt512Lib.sqrt512(0, 1), 1);
        assertEq(Sqrt512Lib.sqrt512(0, 2), 1);
        assertEq(Sqrt512Lib.sqrt512(0, 3), 1);
        assertEq(Sqrt512Lib.sqrt512(0, 4), 2);
        
        // Test powers of 2
        assertEq(Sqrt512Lib.sqrt512(0, 1 << 4), 1 << 2);
        assertEq(Sqrt512Lib.sqrt512(0, 1 << 64), 1 << 32);
        assertEq(Sqrt512Lib.sqrt512(0, 1 << 128), 1 << 64);
        assertEq(Sqrt512Lib.sqrt512(1, 0), 1 << 128);
        assertEq(Sqrt512Lib.sqrt512(1 << 64, 0), 1 << 160);
        
        // Test maximum values
        assertEq(Sqrt512Lib.sqrt512(0, type(uint256).max), 0xffffffffffffffffffffffffffffffff);
        assertEq(Sqrt512Lib.sqrt512(type(uint256).max, 0), 0xffffffffffffffffffffffffffffffff80000000000000000000000000000000);
        assertEq(Sqrt512Lib.sqrt512(type(uint256).max, type(uint256).max), type(uint256).max);
        
        // Test the previously failing cases
        assertEq(Sqrt512Lib.sqrt512(1, type(uint256).max), 0x100000000000000000000000000000000);
        assertEq(Sqrt512Lib.sqrt512(3, type(uint256).max), 0x1ffffffffffffffffffffffffffffffff);
        assertEq(Sqrt512Lib.sqrt512(7, type(uint256).max), 0x2d413cccfe7799211d413cccfe7799211);
        assertEq(Sqrt512Lib.sqrt512(15, type(uint256).max), 0x3ffffffffffffffffffffffffffffffff);
        assertEq(Sqrt512Lib.sqrt512(31, type(uint256).max), 0x5a827999fcef32422cbec4d9baa55f4f8);
        assertEq(Sqrt512Lib.sqrt512(63, type(uint256).max), 0x7ffffffffffffffffffffffffffffffff);
        assertEq(Sqrt512Lib.sqrt512(127, type(uint256).max), 0xb504f333f9de6484597d89b3754abe9f1);
        assertEq(Sqrt512Lib.sqrt512(255, type(uint256).max), 0xfffffffffffffffffffffffffffffffef);
        assertEq(Sqrt512Lib.sqrt512(511, type(uint256).max), 0x16a09e667f3bcc908b2fb1366ea957d3e);
        assertEq(Sqrt512Lib.sqrt512(1023, type(uint256).max), 0x1fffffffffffffffffffffffffffffffdf);
    }
    
    // Gas benchmark function
    function testBenchmark_Sqrt512() public view {
        uint256 gasUsed = gasleft();
        Sqrt512Lib.sqrt512(
            80904256614161075919025625882663817043659112028191499838463115877652359487913,
            49422300655976383518971161772042036479724517635858811238160587340303074464591
        );
        gasUsed = gasUsed - gasleft();
        emit log_named_uint("Gas used", gasUsed);
    }
}
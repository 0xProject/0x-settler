// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "lib/forge-std/src/Test.sol";

library Sqrt512CleanLib {
    function sqrt512(uint256 hi, uint256 lo) internal pure returns (uint256 root) {
        assembly {
            // ======================= 256x256 -> 512 (exact) =======================
            // (hi, lo) = a * b
            function mul512(a, b) -> rhi, rlo {
                rlo := mul(a, b)
                let mm := mulmod(a, b, not(0))
                rhi := sub(sub(mm, rlo), lt(mm, rlo))   // hi = mm - lo - (mm<lo)
            }

            // (hi, lo) = x^2
            function square512(x) -> rhi, rlo {
                rlo := mul(x, x)
                let mm := mulmod(x, x, not(0))
                rhi := sub(sub(mm, rlo), lt(mm, rlo))
            }

            // ======================= 512 -> 256 shifts (branch-light) =======================
            // r = low256( (hi:lo) >> k ), 0 <= k <= 512
            function shr512To256(ahi, alo, k) -> r {
                // For k >= 256: SHR returns 0, SHL(sub(256,k),..) returns 0; only b is live.
                // For k < 256: b is 0 (shift >= 256), only a is live.
                let a := or(shr(k, alo), shl(sub(256, k), ahi))
                let b := shr(sub(k, 256), ahi)
                r := or(a, b)
            }

            // r = low256( (hi:lo) << k ), 0 <= k <= 255  (>=256 => 0 by EVM semantics)
            function shl512To256(ahi, alo, k) -> r {
                r := shl(k, alo)
            }

            // ======================= 512-bit add/sub/compare (branch-light) =======================
            function add512(ahi, alo, bhi, blo) -> rhi, rlo {
                rlo := add(alo, blo)
                rhi := add(add(ahi, bhi), lt(rlo, alo))   // carry
            }
            function add512Const(ahi, alo, c) -> rhi, rlo {
                rlo := add(alo, c)
                rhi := add(ahi, lt(rlo, c))               // carry
            }
            function sub512(ahi, alo, bhi, blo) -> rhi, rlo {
                rlo := sub(alo, blo)
                rhi := sub(sub(ahi, bhi), lt(alo, blo))   // borrow
            }
            function lt512(ahi, alo, bhi, blo) -> r {
                r := or(lt(ahi, bhi), and(eq(ahi, bhi), lt(alo, blo)))
            }

            // ======================= Q1.255 multiplies (directed rounding) =======================
            // floor((a*b) / 2^255)
            function mulShrDown255(a, b) -> z {
                let rhi, rlo := mul512(a, b)
                z := shr512To256(rhi, rlo, 255)
            }
            // ceil((a*b) / 2^255)
            function mulShrUp255(a, b) -> z {
                let rhi, rlo := mul512(a, b)
                z := shr512To256(rhi, rlo, 255)
                // add 1 if any of the low 255 bits of 'lo' are set (constant mask)
                z := add(z, iszero(iszero(and(rlo, 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff))))
            }
            function half_up(x) -> y { y := shr(1, add(x, 1)) }

            // ======================= clz256 (branchless; gas-optimized) =======================
            // Returns 0..256; clz256(0)=256. No memory, no loops.
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

            // ======================= Robust normalization: compute twoe & e =======================
            // twoe = 2*floor(bitlen(N)/2); one branch is cheaper than two CLZs.
            function compute_twoe(ahi, alo) -> twoe, e {
                if ahi {
                    twoe := and(sub(512, clz256(ahi)), not(1))
                }
                if iszero(ahi) {
                    twoe := and(sub(256, clz256(alo)), not(1))
                }
                e := shr(1, twoe)
            }

            // ======================= Under-biased rsqrt step (robust; no (M+1) overflow) =======================
            // Yn = floor( Y * (1.5 - ceil(0.5 * U) ) / 2^255 ),
            // U >= m*y^2*2^255 is built as ceil(M*Y2_up/2^255) + ceil(Y2_up/2^255), avoiding (M+1).
            function rsqrt_step_under(M, Y, TH) -> Yn {
                let Y2_up  := mulShrUp255(Y, Y)          // ceil(Y^2 / 2^255)
                let MY2_up := mulShrUp255(M, Y2_up)      // ceil(M * Y2_up / 2^255)
                // inc = ceil(Y2_up / 2^255) = 1 + (Y2_up > 2^255)
                let inc := add(1, gt(Y2_up, shl(255, 1)))
                let U := add(MY2_up, inc)
                let H_up := half_up(U)                   // ceil(U/2)
                let T_down := sub(TH, H_up)              // 1.5*2^255 - ceil(..)
                Yn := mulShrDown255(Y, T_down)
            }

            // ======================= Main: exact floor sqrt for 512-bit input =======================
            // Returns floor( sqrt( (hi<<256) | lo ) )
            function isqrt512(ahi, alo) -> r {
                // Zero shortcut
                if iszero(or(ahi, alo)) { r := 0 leave }

                // ---- Robust normalization: N = m * 2^(2e), m in [1/2, 2)
                let twoe, e := compute_twoe(ahi, alo)

                // M = floor( m * 2^255 ) = floor( N * 2^(255 - twoe) )
                // Branch-light: only one of these contributes (other path shifts by >=256 -> 0)
                let M := or(
                    shl512To256(ahi, alo, sub(255, twoe)),   // active when twoe <= 255
                    shr512To256(ahi, alo, sub(twoe, 255))    // active when twoe >= 255
                )

                // ---- 6-entry LUT seed: idx = floor(m*4) + 1 = (M >> 253) + 1  in {3..8}
                let idx := add(shr(253, M), 1)
                let Y
                switch idx
                case 3 { Y := 0x93cd3a2c8198e2690c7c0f257d92be830c9d66eec69e17dd97b58cc2cf6c8cf6 }
                case 4 { Y := 0x8000000000000000000000000000000000000000000000000000000000000000 }
                case 5 { Y := 0x727c9716ffb764d594a519c0252be9ae6d00dc9194a760ed9691c407204d6c3b }
                case 6 { Y := 0x6882f5c030b0f7f010b306bb5e1c76d14900b826fd3c1ea0517f3098179a8128 }
                case 7 { Y := 0x60c2479a9fdf9a228b3c8e96d2c84dd553c7ffc87ee4c448a699ceb6a698da73 }
                default { Y := 0x5a827999fcef32422cbec4d9baa55f4f8eb7b05d449dd426768bd642c199cc8a } // idx == 8

                // ---- 8 under-biased Newton steps (Q1.255)
                let TH := add(shl(255, 1), shl(254, 1))  // 1.5 * 2^255
                // Pre-flight schedule: 5 base + up to 3 gated (minimal branching)
                Y := rsqrt_step_under(M, Y, TH)
                Y := rsqrt_step_under(M, Y, TH)
                Y := rsqrt_step_under(M, Y, TH)
                Y := rsqrt_step_under(M, Y, TH)
                Y := rsqrt_step_under(M, Y, TH)
                if gt(e, 58) {
                    Y := rsqrt_step_under(M, Y, TH)
                    if gt(e, 118) {
                        Y := rsqrt_step_under(M, Y, TH)
                        if gt(e, 236) {
                            Y := rsqrt_step_under(M, Y, TH)
                        }
                    }
                }

                // ---- Combine to LOWER-BOUND candidate:
                // r0 = floor( (M * Y) / 2^(510 - e) )
                let pHi, pLo := mul512(M, Y)
                let r0 := shr512To256(pHi, pLo, sub(510, e))

                // ---- Δ = N - r0^2
                let r2hi, r2lo := square512(r0)
                let dHi, dLo := sub512(ahi, alo, r2hi, r2lo)

                // ---- Precompute 2r0, 4r0, 8r0 by shifts (cheaper than 512-adds)
                // S  = 2r0
                let SLo := shl(1, r0)
                let SHi := shr(255, r0)
                // 4r0
                let S2Lo := shl(2, r0)
                let S2Hi := shr(254, r0)
                // 8r0
                let S4Lo := shl(3, r0)
                let S4Hi := shr(253, r0)

                // ======================= HYBRID FIXUP =======================
                // Split at τ4 = 8r0 + 16 (1 jump), then finish branch-free in that half.

                // τ4 = 8r0 + 16
                let t4Lo := add(S4Lo, 16)
                let t4Hi := add(S4Hi, lt(t4Lo, 16))

                // lowerHalf = (Δ < τ4)
                if lt512(dHi, dLo, t4Hi, t4Lo) {
                    // ---- k ∈ {0,1,2,3}
                    // τ2 = 4r0 + 4
                    let t2Lo := add(S2Lo, 4)
                    let t2Hi := add(S2Hi, lt(t2Lo, 4))

                    // Δ < τ2 ?
                    if lt512(dHi, dLo, t2Hi, t2Lo) {
                        // k ∈ {0,1}.  τ1 = 2r0 + 1
                        let t1Lo := add(SLo, 1)
                        let t1Hi := add(SHi, lt(t1Lo, SLo))
                        // Check Δ < τ1
                        if lt512(dHi, dLo, t1Hi, t1Lo) { r := r0 leave }
                        r := add(r0, 1) leave
                    }

                    // k ∈ {2,3}.  τ3 = 6r0 + 9 = (4r0 + 2r0) + 9
                    let t3Lo := add(S2Lo, SLo)
                    let c3a := lt(t3Lo, S2Lo)
                    let t3Hi := add(add(S2Hi, SHi), c3a)
                    t3Lo := add(t3Lo, 9)
                    let c3b := lt(t3Lo, 9)
                    let t3Hi2 := add(t3Hi, c3b)

                    // Check Δ < τ3
                    if lt512(dHi, dLo, t3Hi2, t3Lo) { r := add(r0, 2) leave }
                    r := add(r0, 3) leave
                }

                // ---- k ∈ {4,5,6,7} (upper half)
                // τ6 = 12r0 + 36 = (8r0 + 4r0) + 36
                let t6Lo := add(S4Lo, S2Lo)
                let c6a := lt(t6Lo, S4Lo)
                let t6Hi := add(add(S4Hi, S2Hi), c6a)
                t6Lo := add(t6Lo, 36)
                let c6b := lt(t6Lo, 36)
                let t6Hi2 := add(t6Hi, c6b)

                // Δ < τ6 ?
                if lt512(dHi, dLo, t6Hi2, t6Lo) {
                    // k ∈ {4,5}.  τ5 = 10r0 + 25 = (8r0 + 2r0) + 25
                    let t5Lo := add(S4Lo, SLo)
                    let c5a := lt(t5Lo, S4Lo)
                    let t5Hi := add(add(S4Hi, SHi), c5a)
                    t5Lo := add(t5Lo, 25)
                    let c5b := lt(t5Lo, 25)
                    let t5Hi2 := add(t5Hi, c5b)

                    // Check Δ < τ5
                    if lt512(dHi, dLo, t5Hi2, t5Lo) { r := add(r0, 4) leave }
                    r := add(r0, 5) leave
                }

                // k ∈ {6,7}.  τ7 = 14r0 + 49 = (8r0 + 4r0 + 2r0) + 49
                {
                    let t7Lo := add(S4Lo, S2Lo)
                    let c7a := lt(t7Lo, S4Lo)
                    // FIX: include +SHi in the high limb sum
                    let t7Hi := add(add(add(S4Hi, S2Hi), SHi), c7a)
                    t7Lo := add(t7Lo, SLo)
                    let c7b := lt(t7Lo, SLo)
                    t7Hi := add(t7Hi, c7b)
                    t7Lo := add(t7Lo, 49)
                    let c7c := lt(t7Lo, 49)
                    t7Hi := add(t7Hi, c7c)

                    // Check Δ < τ7
                    if lt512(dHi, dLo, t7Hi, t7Lo) { r := add(r0, 6) leave }
                    r := add(r0, 7)
                }
            }

            // Call the function
            root := isqrt512(hi, lo)
        }
    }
}

contract Sqrt512CleanTest is Test {
    using Sqrt512CleanLib for uint256;

    // Test specific failing case from gas optimization (now fixed)
    function test_GasOptFailingCase() public {
        uint256 hi = 80904256614161075919025625882663817043659112028191499838463115877652359487913;
        uint256 lo = 49422300655976383518971161772042036479724517635858811238160587340303074464591;
        
        uint256 result = Sqrt512CleanLib.sqrt512(hi, lo);
        
        // Check result^2
        uint256 resultSqHi;
        uint256 resultSqLo;
        assembly {
            resultSqLo := mul(result, result)
            let mm := mulmod(result, result, not(0))
            resultSqHi := sub(sub(mm, resultSqLo), lt(mm, resultSqLo))
        }
        
        bool resultSqLteInput = resultSqHi < hi || (resultSqHi == hi && resultSqLo <= lo);
        assertTrue(resultSqLteInput, "result^2 should be <= input");
        
        // Check (result+1)^2  
        uint256 resultP1 = result + 1;
        uint256 resultP1SqHi;
        uint256 resultP1SqLo;
        assembly {
            resultP1SqLo := mul(resultP1, resultP1)
            let mm := mulmod(resultP1, resultP1, not(0))
            resultP1SqHi := sub(sub(mm, resultP1SqLo), lt(mm, resultP1SqLo))
        }
        
        bool resultP1SqGtInput = resultP1SqHi > hi || (resultP1SqHi == hi && resultP1SqLo > lo);
        assertTrue(resultP1SqGtInput, "(result+1)^2 should be > input");
    }
    
    // Test the new failing case
    function test_NewFailingCase() public {
        uint256 hi = 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdf;
        uint256 lo = 0x00000000000000000000000000000000000000000000000000000000000007a0;
        uint256 result = Sqrt512CleanLib.sqrt512(hi, lo);
        
        // Let's also check what result-1 squared is
        if (result > 0) {
            uint256 resultM1 = result - 1;
            uint256 resultM1SqHi;
            uint256 resultM1SqLo;
            assembly {
                resultM1SqLo := mul(resultM1, resultM1)
                let mm := mulmod(resultM1, resultM1, not(0))
                resultM1SqHi := sub(sub(mm, resultM1SqLo), lt(mm, resultM1SqLo))
            }
            emit log_named_uint("(result-1)^2 hi", resultM1SqHi);
            emit log_named_uint("(result-1)^2 lo", resultM1SqLo);
            bool resultM1SqLteInput = resultM1SqHi < hi || (resultM1SqHi == hi && resultM1SqLo <= lo);
            emit log_named_string("(result-1)^2 <= input", resultM1SqLteInput ? "true" : "false");
            
            // Check several more values
            for (uint256 i = 2; i <= 5 && result >= i; i++) {
                uint256 candidate = result - i;
                uint256 candSqHi;
                uint256 candSqLo;
                assembly {
                    candSqLo := mul(candidate, candidate)
                    let mm := mulmod(candidate, candidate, not(0))
                    candSqHi := sub(sub(mm, candSqLo), lt(mm, candSqLo))
                }
                bool candSqLteInput = candSqHi < hi || (candSqHi == hi && candSqLo <= lo);
                emit log_named_uint("checking result-i where i=", i);
                emit log_named_uint("  (result-i)^2 hi", candSqHi);
                emit log_named_uint("  (result-i)^2 lo", candSqLo);
                emit log_named_string("  (result-i)^2 <= input", candSqLteInput ? "true" : "false");
            }
        }
        
        emit log_named_uint("hi", hi);
        emit log_named_uint("lo", lo);
        emit log_named_uint("result", result);
        
        // Check result^2
        uint256 resultSqHi;
        uint256 resultSqLo;
        assembly {
            resultSqLo := mul(result, result)
            let mm := mulmod(result, result, not(0))
            resultSqHi := sub(sub(mm, resultSqLo), lt(mm, resultSqLo))
        }
        
        emit log_named_uint("result^2 hi", resultSqHi);
        emit log_named_uint("result^2 lo", resultSqLo);
        
        // Check (result+1)^2
        uint256 resultP1 = result + 1;
        uint256 resultP1SqHi;
        uint256 resultP1SqLo;
        assembly {
            resultP1SqLo := mul(resultP1, resultP1)
            let mm := mulmod(resultP1, resultP1, not(0))
            resultP1SqHi := sub(sub(mm, resultP1SqLo), lt(mm, resultP1SqLo))
        }
        
        emit log_named_uint("(result+1)^2 hi", resultP1SqHi);
        emit log_named_uint("(result+1)^2 lo", resultP1SqLo);
        
        // Check result^2 <= input
        bool resultSqLteInput = resultSqHi < hi || (resultSqHi == hi && resultSqLo <= lo);
        emit log_named_string("result^2 <= input", resultSqLteInput ? "true" : "false");
        
        // Check (result+1)^2 > input
        bool resultP1SqGtInput = resultP1SqHi > hi || (resultP1SqHi == hi && resultP1SqLo > lo);
        emit log_named_string("(result+1)^2 > input", resultP1SqGtInput ? "true" : "false");
        
        assertTrue(resultSqLteInput, "result^2 should be <= input");
        assertTrue(resultP1SqGtInput, "(result+1)^2 should be > input");
    }
    
    // Test specific edge cases
    function test_EdgeCases() public pure {
        // Test the specific failing case
        uint256 hi = 1;
        uint256 lo = type(uint256).max;
        uint256 result = Sqrt512CleanLib.sqrt512(hi, lo);
        
        // Verify property 1: result^2 <= input
        uint256 resultSqHi;
        uint256 resultSqLo;
        assembly {
            resultSqLo := mul(result, result)
            let mm := mulmod(result, result, not(0))
            resultSqHi := sub(sub(mm, resultSqLo), lt(mm, resultSqLo))
        }
        
        // Check result^2 <= input
        bool resultSqLteInput = resultSqHi < hi || (resultSqHi == hi && resultSqLo <= lo);
        assertTrue(resultSqLteInput, "result^2 should be <= input for hi=1, lo=max");
        
        // Verify property 2: (result+1)^2 > input (unless result is max uint256)
        if (result < type(uint256).max) {
            uint256 resultP1 = result + 1;
            uint256 resultP1SqHi;
            uint256 resultP1SqLo;
            assembly {
                resultP1SqLo := mul(resultP1, resultP1)
                let mm := mulmod(resultP1, resultP1, not(0))
                resultP1SqHi := sub(sub(mm, resultP1SqLo), lt(mm, resultP1SqLo))
            }
            
            // Check (result+1)^2 > input
            bool resultP1SqGtInput = resultP1SqHi > hi || (resultP1SqHi == hi && resultP1SqLo > lo);
            assertTrue(resultP1SqGtInput, "(result+1)^2 should be > input for hi=1, lo=max");
        }
        
        // Test more edge cases with odd powers
        uint256[6] memory oddPowers = [uint256(7), 31, 127, 511, 2047, 8191];
        for (uint256 i = 0; i < oddPowers.length; i++) {
            hi = oddPowers[i];
            result = Sqrt512CleanLib.sqrt512(hi, lo);
            
            // Check result^2 <= input
            assembly {
                resultSqLo := mul(result, result)
                let mm := mulmod(result, result, not(0))
                resultSqHi := sub(sub(mm, resultSqLo), lt(mm, resultSqLo))
            }
            
            resultSqLteInput = resultSqHi < hi || (resultSqHi == hi && resultSqLo <= lo);
            assertTrue(resultSqLteInput, "result^2 should be <= input");
        }
    }

    function testFuzz_Sqrt512_Correctness(uint256 hi, uint256 lo) public pure {
        // The maximum value whose sqrt fits in uint256 is (2^256 - 1)^2
        // = 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0000000000000000000000000000000000000000000000000000000000000001
        // Reject inputs larger than this as they would require result >= 2^256
        vm.assume(hi < 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe || 
                  (hi == 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe && lo <= 1));
        
        uint256 result = Sqrt512CleanLib.sqrt512(hi, lo);
        
        // Verify property 1: result^2 <= input
        uint256 resultSqHi;
        uint256 resultSqLo;
        assembly {
            resultSqLo := mul(result, result)
            let mm := mulmod(result, result, not(0))
            resultSqHi := sub(sub(mm, resultSqLo), lt(mm, resultSqLo))
        }
        
        // Check result^2 <= input
        bool resultSqLteInput = resultSqHi < hi || (resultSqHi == hi && resultSqLo <= lo);
        assertTrue(resultSqLteInput, "result^2 should be <= input");
        
        // Verify property 2: (result+1)^2 > input (unless result is max uint256)
        if (result < type(uint256).max) {
            uint256 resultP1 = result + 1;
            uint256 resultP1SqHi;
            uint256 resultP1SqLo;
            assembly {
                resultP1SqLo := mul(resultP1, resultP1)
                let mm := mulmod(resultP1, resultP1, not(0))
                resultP1SqHi := sub(sub(mm, resultP1SqLo), lt(mm, resultP1SqLo))
            }
            
            // Check (result+1)^2 > input
            bool resultP1SqGtInput = resultP1SqHi > hi || (resultP1SqHi == hi && resultP1SqLo > lo);
            assertTrue(resultP1SqGtInput, "(result+1)^2 should be > input");
        }
    }
}
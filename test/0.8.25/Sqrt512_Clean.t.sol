// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "lib/forge-std/src/Test.sol";

library Sqrt512Lib {
    function sqrt512(uint256 hi, uint256 lo) internal pure returns (uint256 root) {
        assembly {
            // ================================================================
            //  256x256 -> 512 helpers (exact) using the mulmod high-word trick
            // ================================================================
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

            // ================================================================
            //  512 -> 256 shifts (branchless selection)
            // ================================================================
            function shr512To256(ahi, alo, k) -> r {
                let a := or(shr(k, alo), shl(sub(256, k), ahi))
                let b := shr(sub(k, 256), ahi)
                r := or(a, b)
            }

            function shl512To256(ahi, alo, k) -> r {
                r := shl(k, alo)
            }

            // ================================================================
            //  512-bit add/sub and comparisons (branchless)
            // ================================================================
            function add512(ahi, alo, bhi, blo) -> rhi, rlo {
                rlo := add(alo, blo)
                rhi := add(add(ahi, bhi), lt(rlo, alo))
            }
            function add512Const(ahi, alo, c) -> rhi, rlo {
                rlo := add(alo, c)
                rhi := add(ahi, lt(rlo, c))
            }
            function sub512(ahi, alo, bhi, blo) -> rhi, rlo {
                rlo := sub(alo, blo)
                rhi := sub(sub(ahi, bhi), lt(alo, blo))
            }
            function lt512(ahi, alo, bhi, blo) -> r {
                r := or(lt(ahi, bhi), and(eq(ahi, bhi), lt(alo, blo)))
            }

            // ================================================================
            //  Q1.255 multiplies with directed rounding (F = 255)
            // ================================================================
            function mulShrDown255(a, b) -> z {
                let rhi, rlo := mul512(a, b)
                z := shr512To256(rhi, rlo, 255)
            }
            function mulShrUp255(a, b) -> z {
                let rhi, rlo := mul512(a, b)
                z := shr512To256(rhi, rlo, 255)
                let remMask := sub(shl(255, 1), 1)
                z := add(z, iszero(iszero(and(rlo, remMask))))
            }
            function half_up(x) -> y { y := shr(1, add(x, 1)) }

            // ================================================================
            //  Bit length of (hi:lo)
            // ================================================================
            function clz256(x) -> n {
                n := 256
                if x {
                    n := 0
                    if iszero(shr(128, x)) { n := add(n, 128) x := shl(128, x) }
                    if iszero(shr(192, x)) { n := add(n, 64)  x := shl(64, x)  }
                    if iszero(shr(224, x)) { n := add(n, 32)  x := shl(32, x)  }
                    if iszero(shr(240, x)) { n := add(n, 16)  x := shl(16, x)  }
                    if iszero(shr(248, x)) { n := add(n, 8)   x := shl(8, x)   }
                    if iszero(shr(252, x)) { n := add(n, 4)   x := shl(4, x)   }
                    if iszero(shr(254, x)) { n := add(n, 2)   x := shl(2, x)   }
                    if iszero(shr(255, x)) { n := add(n, 1) }
                }
            }
            function bitlen512(ahi, alo) -> L {
                let hiz := iszero(ahi)
                let loz := iszero(alo)
                switch hiz
                case 1 {
                    switch loz
                    case 1 { L := 0 }
                    default { L := sub(256, clz256(alo)) }
                }
                default {
                    L := add(256, sub(256, clz256(ahi)))
                }
            }

            // ================================================================
            //  Under-biased Newton step on rsqrt (Q1.255)
            // ================================================================
            function rsqrt_step_under(M, Y, TH) -> Yn {
                let Y2_up  := mulShrUp255(Y, Y)
                let MY2_up := mulShrUp255(add(M, 1), Y2_up)
                let H_up   := half_up(MY2_up)
                let T_down := sub(TH, H_up)
                Yn := mulShrDown255(Y, T_down)
            }

            // ================================================================
            //  Main sqrt function
            // ================================================================
            function isqrt512(ahi, alo) -> r {
                // Zero short-circuit
                if iszero(or(ahi, alo)) { r := 0 leave }

                // Normalize: N = m * 2^(2e) with m in [1/2, 2)
                let L := bitlen512(ahi, alo)
                let e := shr(1, L)
                let twoe := add(e, e)

                // M = floor(m * 2^255) = floor(N * 2^(255 - 2e))
                let M := or(
                    shl512To256(ahi, alo, sub(255, twoe)),
                    shr512To256(ahi, alo, sub(twoe, 255))
                )

                // 6-entry LUT seed
                let idx := add(shr(253, M), 1)
                let Y
                switch idx
                case 3 { Y := 0x93cd3a2c8198e2690c7c0f257d92be830c9d66eec69e17dd97b58cc2cf6c8cf6 }
                case 4 { Y := 0x8000000000000000000000000000000000000000000000000000000000000000 }
                case 5 { Y := 0x727c9716ffb764d594a519c0252be9ae6d00dc9194a760ed9691c407204d6c3b }
                case 6 { Y := 0x6882f5c030b0f7f010b306bb5e1c76d14900b826fd3c1ea0517f3098179a8128 }
                case 7 { Y := 0x60c2479a9fdf9a228b3c8e96d2c84dd553c7ffc87ee4c448a699ceb6a698da73 }
                default { Y := 0x5a827999fcef32422cbec4d9baa55f4f8eb7b05d449dd426768bd642c199cc8a }

                // 8 under-biased Newton steps
                let TH := add(shl(255, 1), shl(254, 1))
                Y := rsqrt_step_under(M, Y, TH)
                Y := rsqrt_step_under(M, Y, TH)
                Y := rsqrt_step_under(M, Y, TH)
                Y := rsqrt_step_under(M, Y, TH)
                Y := rsqrt_step_under(M, Y, TH)
                Y := rsqrt_step_under(M, Y, TH)
                Y := rsqrt_step_under(M, Y, TH)
                Y := rsqrt_step_under(M, Y, TH)

                // Combine to lower-bound candidate
                let pHi, pLo := mul512(M, Y)
                let r0 := shr512To256(pHi, pLo, sub(510, e))

                // One-sided affine fixup (+0/+1/+2/+3)
                let r2hi, r2lo := square512(r0)
                let dHi, dLo := sub512(ahi, alo, r2hi, r2lo)

                // S = 2*r0 as 512-bit
                let SLo := shl(1, r0)
                let SHi := shr(255, r0)

                // Precompute 2S and 4S
                let S2Hi, S2Lo := add512(SHi, SLo, SHi, SLo)
                let S4Hi, S4Lo := add512(S2Hi, S2Lo, S2Hi, S2Lo)

                // τ1 = 2r0 + 1, τ2 = 4r0 + 4, τ3 = 6r0 + 9
                let t1Lo := add(SLo, 1)
                let t1Hi := add(SHi, lt(t1Lo, 1))
                let t2Hi, t2Lo := add512Const(S2Hi, S2Lo, 4)
                let t3Hi, t3Lo := add512(S2Hi, S2Lo, SHi, SLo)
                t3Hi, t3Lo := add512Const(t3Hi, t3Lo, 9)

                // Compare and select k
                let b1 := lt512(dHi, dLo, t1Hi, t1Lo)
                let b2 := lt512(dHi, dLo, t2Hi, t2Lo)
                let b3 := lt512(dHi, dLo, t3Hi, t3Lo)

                let nb1 := xor(b1, 1)
                let nb2 := xor(b2, 1)
                let nb3 := xor(b3, 1)
                let k  := nb1
                k := add(k, and(nb2, nb1))
                k := add(k, and(nb3, and(nb2, nb1)))

                r := add(r0, k)
            }

            // Call the function
            root := isqrt512(hi, lo)
        }
    }
}

contract Sqrt512CleanTest is Test {
    using Sqrt512Lib for uint256;

    // Test specific edge cases
    function test_EdgeCases() public {
        // Test cases of form 2^n - 1
        uint256 lo = type(uint256).max;
        uint256[] memory failingHi = new uint256[](20);
        uint256 failCount = 0;
        
        // Test even powers of 2 minus 1 (should work)
        uint256[5] memory evenPowers = [uint256(2), 4, 6, 8, 10];
        for (uint256 i = 0; i < evenPowers.length; i++) {
            uint256 n = evenPowers[i];
            uint256 hi = (1 << n) - 1; // 2^n - 1
            uint256 result = Sqrt512Lib.sqrt512(hi, lo);
            
            // Check result^2 <= input
            uint256 resultSqHi;
            uint256 resultSqLo;
            assembly {
                resultSqLo := mul(result, result)
                let mm := mulmod(result, result, not(0))
                resultSqHi := sub(sub(mm, resultSqLo), lt(mm, resultSqLo))
            }
            
            bool valid = resultSqHi < hi || (resultSqHi == hi && resultSqLo <= lo);
            if (!valid && failCount < 20) {
                failingHi[failCount++] = hi;
            }
            
        }
        
        // Report all failing cases
        emit log_named_uint("Total failures", failCount);
        for (uint256 i = 0; i < failCount; i++) {
            emit log_named_uint("Failed hi", failingHi[i]);
        }
        
        if (failCount > 0) {
            revert("Multiple failures found");
        }
    }

    function testFuzz_Sqrt512_Correctness(uint256 hi, uint256 lo) public pure {
        uint256 result = Sqrt512Lib.sqrt512(hi, lo);
        
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
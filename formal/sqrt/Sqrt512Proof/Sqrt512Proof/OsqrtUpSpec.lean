/-
  Bridge proof: model_osqrtUp_evm computes sqrtUp512.

  The auto-generated model_osqrtUp_evm returns (r_hi, r_lo) where
  r_hi * 2^256 + r_lo = sqrtUp512(x_hi * 2^256 + x_lo).

  Case x_hi = 0: r_hi = 0, r_lo = inlined 256-bit sqrtUp(x_lo).
  Case x_hi > 0: r = floor_sqrt(x), needsUp = (x > r²), result = r + needsUp with carry.
-/
import Sqrt512Proof.GeneratedSqrt512Model
import Sqrt512Proof.GeneratedSqrt512Spec
import Sqrt512Proof.SqrtUpCorrect
import Sqrt512Proof.SqrtWrapperSpec
import SqrtProof.GeneratedSqrtModel
import SqrtProof.GeneratedSqrtSpec
import SqrtProof.SqrtCorrect

namespace Sqrt512Spec

open Sqrt512GeneratedModel

-- ============================================================================
-- Section 1: x_hi = 0 branch — bridge to model_sqrt_up_evm
-- ============================================================================

/-- When x_hi = 0, the first component (r_hi) is 0. -/
private theorem osqrtUp_zero_fst (x_lo : Nat) :
    (model_osqrtUp_evm 0 x_lo).1 = 0 := by
  simp only [model_osqrtUp_evm]
  simp only [evmEq_compat, u256_compat, su256_zero]
  simp only [SqrtGeneratedModel.evmEq, SqrtGeneratedModel.u256, SqrtGeneratedModel.WORD_MOD]
  simp (config := { decide := true })

/-- When x_hi = 0, the second component (r_lo) equals model_sqrt_up_evm x_lo. -/
private theorem osqrtUp_zero_snd (x_lo : Nat) :
    (model_osqrtUp_evm 0 x_lo).2 = SqrtGeneratedModel.model_sqrt_up_evm x_lo := by
  simp only [model_osqrtUp_evm, model_sqrt256_up_evm,
    SqrtGeneratedModel.model_sqrt_up_evm, SqrtGeneratedModel.model_sqrt_evm]
  simp only [evmEq_compat, evmShr_compat, evmAdd_compat, evmDiv_compat,
    evmSub_compat, evmClz_compat, evmShl_compat, evmLt_compat,
    evmMul_compat, evmGt_compat, u256_compat]
  simp only [su256_zero, su256_idem]
  simp only [SqrtGeneratedModel.evmEq, SqrtGeneratedModel.u256, SqrtGeneratedModel.WORD_MOD]
  simp (config := { decide := true })

/-- Ceiling sqrt uniqueness: if x ≤ r² and r is minimal, then r = sqrtUp512 x. -/
private theorem sqrtUp512_unique (x r : Nat) (hx : x < 2 ^ 512)
    (hle : x ≤ r * r) (hmin : ∀ y, x ≤ y * y → r ≤ y) :
    r = sqrtUp512 x := by
  have ⟨hup_le, hup_min⟩ := sqrtUp512_correct x hx
  have h1 := hmin (sqrtUp512 x) hup_le
  have h2 := hup_min r hle
  omega

-- ============================================================================
-- Section 2: Helper lemmas for x_hi > 0 — _mul correctness
-- ============================================================================

/-- mulmod(r, r, 2^256-1) combined with mul(r,r) and sub/lt recovers r²/2^256.
    Key identity: 2^256 ≡ 1 (mod 2^256-1). -/
private theorem mul512_high_word (r : Nat) (hr : r < WORD_MOD) :
    let mm := evmMulmod r r (evmNot 0)
    let m := evmMul r r
    evmSub (evmSub mm m) (evmLt mm m) = r * r / WORD_MOD := by
  simp only
  -- Step 1: Simplify evmNot 0
  have hNot0 : evmNot 0 = WORD_MOD - 1 := by
    unfold evmNot u256 WORD_MOD; simp
  -- Step 2: Simplify evmMulmod and evmMul
  have hWM1_pos : (0 : Nat) < WORD_MOD - 1 := by unfold WORD_MOD; omega
  have hWM1_lt : WORD_MOD - 1 < WORD_MOD := by unfold WORD_MOD; omega
  have hmm : evmMulmod r r (evmNot 0) = (r * r) % (WORD_MOD - 1) := by
    unfold evmMulmod
    simp only [u256_id' r hr, hNot0, u256_id' (WORD_MOD - 1) hWM1_lt]
    simp [Nat.ne_of_gt hWM1_pos]
  have hm : evmMul r r = (r * r) % WORD_MOD := by
    unfold evmMul u256; simp [Nat.mod_eq_of_lt hr]
  rw [hmm, hm]
  -- Abbreviate for readability (without set tactic)
  -- hi = (r*r) % (WORD_MOD - 1), lo = (r*r) % WORD_MOD, q = r*r / WORD_MOD
  have hdecomp : r * r = r * r / WORD_MOD * WORD_MOD + r * r % WORD_MOD := by
    have := Nat.div_add_mod (r * r) WORD_MOD
    rw [Nat.mul_comm] at this; omega
  have hq_bound : r * r / WORD_MOD < WORD_MOD := by
    have : r * r < WORD_MOD * WORD_MOD :=
      Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt hr) hr (by unfold WORD_MOD; omega)
    exact Nat.div_lt_of_lt_mul this
  have hlo_bound : r * r % WORD_MOD < WORD_MOD := Nat.mod_lt _ (by unfold WORD_MOD; omega)
  -- Key congruence: hi = (q + lo) % (WORD_MOD - 1)
  -- Since WORD_MOD = (WORD_MOD - 1) + 1, q*WORD_MOD = q*(WORD_MOD-1) + q
  -- So r*r = q*(WORD_MOD-1) + (q + lo), and r*r % (WORD_MOD-1) = (q+lo) % (WORD_MOD-1)
  have hhi_eq : (r * r) % (WORD_MOD - 1) = (r * r / WORD_MOD + r * r % WORD_MOD) % (WORD_MOD - 1) := by
    -- q * W = (W-1)*q + q
    have hqW : r * r / WORD_MOD * WORD_MOD =
        (WORD_MOD - 1) * (r * r / WORD_MOD) + r * r / WORD_MOD := by
      have hsc := Nat.sub_add_cancel (Nat.one_le_of_lt (show 1 < WORD_MOD from by unfold WORD_MOD; omega))
      -- q * ((W-1) + 1) = q*(W-1) + q*1
      have h := Nat.mul_add (r * r / WORD_MOD) (WORD_MOD - 1) 1
      rw [hsc, Nat.mul_one] at h
      -- h : r * r / WORD_MOD * WORD_MOD = r * r / WORD_MOD * (WORD_MOD - 1) + r * r / WORD_MOD
      rw [h, Nat.mul_comm (r * r / WORD_MOD) (WORD_MOD - 1)]
    -- r*r = (W-1)*q + (q+lo)
    have hrr_eq : r * r = (WORD_MOD - 1) * (r * r / WORD_MOD) + (r * r / WORD_MOD + r * r % WORD_MOD) := by
      omega
    -- Apply Nat.mul_add_mod: ((W-1)*q + (q+lo)) % (W-1) = (q+lo) % (W-1)
    have step := Nat.mul_add_mod (WORD_MOD - 1) (r * r / WORD_MOD) (r * r / WORD_MOD + r * r % WORD_MOD)
    -- step : ((WORD_MOD - 1) * (r * r / WORD_MOD) + (r * r / WORD_MOD + r * r % WORD_MOD)) % (WORD_MOD - 1) =
    --        (r * r / WORD_MOD + r * r % WORD_MOD) % (WORD_MOD - 1)
    rw [← hrr_eq] at step; exact step
  have hhi_bound : (r * r) % (WORD_MOD - 1) < WORD_MOD - 1 := Nat.mod_lt _ hWM1_pos
  -- Case split on whether q + lo wraps modulo (WORD_MOD - 1)
  by_cases hcase : r * r / WORD_MOD + r * r % WORD_MOD < WORD_MOD - 1
  · -- Case 1: no wrap
    have hhi_val : (r * r) % (WORD_MOD - 1) = r * r / WORD_MOD + r * r % WORD_MOD := by
      rw [hhi_eq, Nat.mod_eq_of_lt hcase]
    have hhi_wm : (r * r) % (WORD_MOD - 1) < WORD_MOD := by omega
    have hge : r * r % WORD_MOD ≤ (r * r) % (WORD_MOD - 1) := by
      rw [hhi_val]; exact Nat.le_add_left _ _
    have hlt_eq : evmLt ((r * r) % (WORD_MOD - 1)) (r * r % WORD_MOD) = 0 := by
      unfold evmLt u256
      simp only [Nat.mod_eq_of_lt hhi_wm, Nat.mod_eq_of_lt hlo_bound]
      exact if_neg (Nat.not_lt.mpr hge)
    rw [hlt_eq]
    have hsub1 : evmSub ((r * r) % (WORD_MOD - 1)) (r * r % WORD_MOD) =
        (r * r) % (WORD_MOD - 1) - r * r % WORD_MOD :=
      evmSub_eq_of_le _ _ hhi_wm hge
    rw [hsub1]
    have hq_eq : (r * r) % (WORD_MOD - 1) - r * r % WORD_MOD = r * r / WORD_MOD := by
      omega
    rw [hq_eq]
    -- evmSub q 0 = q
    exact evmSub_eq_of_le _ 0 hq_bound (Nat.zero_le _)
  · -- Case 2: wrap (hcase : ¬(q + lo < W-1), i.e., W-1 ≤ q + lo)
    have hcase' : WORD_MOD - 1 ≤ r * r / WORD_MOD + r * r % WORD_MOD := Nat.not_lt.mp hcase
    -- r * r ≤ (WORD_MOD-1)^2 since r < WORD_MOD
    -- q + lo < 2*(WORD_MOD-1) because q ≤ WORD_MOD-2 and lo ≤ WORD_MOD-1
    -- r ≤ WORD_MOD - 1, so r*r ≤ (WORD_MOD-1)^2, so q = r*r/WORD_MOD ≤ WORD_MOD - 2
    have hq_le : r * r / WORD_MOD ≤ WORD_MOD - 2 := by
      have hr' : r ≤ WORD_MOD - 1 := by omega
      have hrsq : r * r ≤ (WORD_MOD - 1) * (WORD_MOD - 1) := Nat.mul_le_mul hr' hr'
      have h1 : r * r / WORD_MOD ≤ (WORD_MOD - 1) * (WORD_MOD - 1) / WORD_MOD :=
        @Nat.div_le_div_right _ _ WORD_MOD hrsq
      suffices h : (WORD_MOD - 1) * (WORD_MOD - 1) / WORD_MOD = WORD_MOD - 2 by omega
      unfold WORD_MOD; omega
    have hql_lt : r * r / WORD_MOD + r * r % WORD_MOD < 2 * (WORD_MOD - 1) := by omega
    have hhi_val : (r * r) % (WORD_MOD - 1) =
        r * r / WORD_MOD + r * r % WORD_MOD - (WORD_MOD - 1) := by
      rw [hhi_eq,
          Nat.mod_eq_sub_mod hcase',
          Nat.mod_eq_of_lt (by omega)]
    have hlt_lo : (r * r) % (WORD_MOD - 1) < r * r % WORD_MOD := by
      rw [hhi_val]; omega
    have hhi_wm : (r * r) % (WORD_MOD - 1) < WORD_MOD := by omega
    have hlt_eq : evmLt ((r * r) % (WORD_MOD - 1)) (r * r % WORD_MOD) = 1 := by
      unfold evmLt u256
      simp [Nat.mod_eq_of_lt hhi_wm, Nat.mod_eq_of_lt hlo_bound]
      exact hlt_lo
    rw [hlt_eq]
    -- evmSub wraps: hi + WORD_MOD - lo
    have hsub1 : evmSub ((r * r) % (WORD_MOD - 1)) (r * r % WORD_MOD) =
        (r * r) % (WORD_MOD - 1) + WORD_MOD - r * r % WORD_MOD := by
      unfold evmSub u256
      simp [Nat.mod_eq_of_lt hhi_wm, Nat.mod_eq_of_lt hlo_bound]
      exact Nat.mod_eq_of_lt (show (r * r) % (WORD_MOD - 1) + WORD_MOD - r * r % WORD_MOD < WORD_MOD
        by rw [hhi_val]; omega)
    rw [hsub1]
    have hval : (r * r) % (WORD_MOD - 1) + WORD_MOD - r * r % WORD_MOD < WORD_MOD := by
      rw [hhi_val]; omega
    have hsub2 : evmSub ((r * r) % (WORD_MOD - 1) + WORD_MOD - r * r % WORD_MOD) 1 =
        (r * r) % (WORD_MOD - 1) + WORD_MOD - r * r % WORD_MOD - 1 :=
      evmSub_eq_of_le _ 1 hval (by rw [hhi_val]; omega)
    rw [hsub2]
    rw [hhi_val]; omega

/-- mul(r, r) gives the low word of r². -/
private theorem mul512_low_word (r : Nat) (hr : r < WORD_MOD) :
    evmMul r r = r * r % WORD_MOD := by
  unfold evmMul u256; simp [Nat.mod_eq_of_lt hr]

-- ============================================================================
-- Section 3: Helper lemmas for x_hi > 0 — _gt correctness
-- ============================================================================

/-- The 512-bit lexicographic comparison correctly computes x > r². -/
private theorem gt512_correct (x_hi x_lo sq_hi sq_lo : Nat)
    (hxhi : x_hi < WORD_MOD) (hxlo : x_lo < WORD_MOD)
    (hsqhi : sq_hi < WORD_MOD) (hsqlo : sq_lo < WORD_MOD) :
    let cmp := evmOr (evmGt x_hi sq_hi)
      (evmAnd (evmEq x_hi sq_hi) (evmGt x_lo sq_lo))
    (cmp ≠ 0) ↔ (x_hi * WORD_MOD + x_lo > sq_hi * WORD_MOD + sq_lo) := by
  simp only
  -- Simplify EVM operations to pure comparisons
  have hgt_hi : evmGt x_hi sq_hi = if x_hi > sq_hi then 1 else 0 := by
    unfold evmGt u256; simp [Nat.mod_eq_of_lt hxhi, Nat.mod_eq_of_lt hsqhi]
  have heq_hi : evmEq x_hi sq_hi = if x_hi = sq_hi then 1 else 0 := by
    unfold evmEq u256; simp [Nat.mod_eq_of_lt hxhi, Nat.mod_eq_of_lt hsqhi]
  have hgt_lo : evmGt x_lo sq_lo = if x_lo > sq_lo then 1 else 0 := by
    unfold evmGt u256; simp [Nat.mod_eq_of_lt hxlo, Nat.mod_eq_of_lt hsqlo]
  rw [hgt_hi, heq_hi, hgt_lo]
  -- Full case analysis on orderings
  by_cases hgt : x_hi > sq_hi
  · -- x_hi > sq_hi: LHS or has at least one 1
    have hneq : ¬(x_hi = sq_hi) := by omega
    simp only [hgt, ite_true, hneq, ite_false]
    -- evmOr 1 (evmAnd 0 (if ...)) always reduces to something nonzero
    have hor_nz : ∀ v, evmOr 1 (evmAnd 0 v) ≠ 0 := by
      intro v; unfold evmOr evmAnd u256 WORD_MOD; simp (config := { decide := true })
    constructor
    · intro _
      -- sq_hi + 1 ≤ x_hi, so sq_hi*W + W ≤ x_hi*W
      have h1 : sq_hi * WORD_MOD + WORD_MOD ≤ x_hi * WORD_MOD := by
        have := Nat.mul_le_mul_right WORD_MOD hgt
        rwa [Nat.succ_mul] at this
      omega
    · intro _; exact hor_nz _
  · by_cases heq : x_hi = sq_hi
    · subst heq
      simp only [Nat.lt_irrefl, ite_false, ite_true]
      by_cases hgtlo : x_lo > sq_lo
      · simp only [hgtlo, ite_true]
        constructor
        · intro _; omega
        · intro _; unfold evmOr evmAnd u256 WORD_MOD; simp (config := { decide := true })
      · simp only [hgtlo, ite_false]
        have hor_z : evmOr 0 (evmAnd 1 0) = 0 := by
          unfold evmOr evmAnd u256 WORD_MOD; simp (config := { decide := true })
        constructor
        · intro h; exact absurd hor_z h
        · intro h; omega
    · -- x_hi < sq_hi
      have hlt : x_hi < sq_hi := by omega
      have hng : ¬(x_hi > sq_hi) := by omega
      simp only [hng, ite_false, heq, ite_false]
      -- evmOr 0 (evmAnd 0 (if ...)) = 0
      have hor_z : ∀ v, evmOr 0 (evmAnd 0 v) = 0 := by
        intro v; unfold evmOr evmAnd u256 WORD_MOD; simp (config := { decide := true })
      constructor
      · intro h; exact absurd (hor_z _) h
      · intro h
        have h1 : x_hi * WORD_MOD + WORD_MOD ≤ sq_hi * WORD_MOD := by
          have := Nat.mul_le_mul_right WORD_MOD hlt
          rwa [Nat.succ_mul] at this
        omega

-- ============================================================================
-- Section 4: Helper lemmas for x_hi > 0 — _add correctness
-- ============================================================================

/-- add(r, needsUp) with carry detection gives correct 512-bit result.
    When needsUp ∈ {0,1}, the result r + needsUp is at most 2^256. -/
private theorem add_with_carry (r needsUp : Nat) (hr : r < WORD_MOD)
    (hn : needsUp = 0 ∨ needsUp = 1) :
    let r_lo := evmAdd r needsUp
    let r_hi := evmLt (evmAdd r needsUp) r
    r_hi * WORD_MOD + r_lo = r + needsUp := by
  simp only
  have hn_bound : needsUp < WORD_MOD := by rcases hn with h | h <;> (rw [h]; unfold WORD_MOD; omega)
  by_cases hov : r + needsUp < WORD_MOD
  · -- No overflow
    have hadd : evmAdd r needsUp = r + needsUp :=
      evmAdd_eq' r needsUp hr hn_bound hov
    rw [hadd]
    have hge : r ≤ r + needsUp := Nat.le_add_right r needsUp
    have hlt_eq : evmLt (r + needsUp) r = 0 := by
      unfold evmLt u256
      simp only [Nat.mod_eq_of_lt hov, Nat.mod_eq_of_lt hr]
      exact if_neg (Nat.not_lt.mpr hge)
    rw [hlt_eq]; simp
  · -- Overflow: r + needsUp ≥ WORD_MOD, so needsUp = 1 and r = WORD_MOD - 1
    have hov' : WORD_MOD ≤ r + needsUp := Nat.not_lt.mp hov
    have hn1 : needsUp = 1 := by rcases hn with h | h <;> omega
    subst hn1
    have hr_max : r = WORD_MOD - 1 := by omega
    subst hr_max
    -- evmAdd (WORD_MOD - 1) 1 = 0 (overflow)
    have hadd : evmAdd (WORD_MOD - 1) 1 = 0 := by
      unfold evmAdd u256 WORD_MOD; simp
    rw [hadd]
    -- evmLt 0 (WORD_MOD - 1) = 1 (since 0 < WORD_MOD - 1)
    have hlt_eq : evmLt 0 (WORD_MOD - 1) = 1 := by
      unfold evmLt u256 WORD_MOD; simp
    rw [hlt_eq]
    unfold WORD_MOD; omega

-- ============================================================================
-- Section 5: Main theorem — model_osqrtUp_evm = sqrtUp512
-- ============================================================================

set_option exponentiation.threshold 1024 in
/-- The EVM model of osqrtUp(uint512, uint512) computes sqrtUp512. -/
theorem model_osqrtUp_evm_correct (x_hi x_lo : Nat)
    (hxhi : x_hi < 2 ^ 256) (hxlo : x_lo < 2 ^ 256) :
    let (r_hi, r_lo) := model_osqrtUp_evm x_hi x_lo
    let x := x_hi * 2 ^ 256 + x_lo
    r_hi * 2 ^ 256 + r_lo = sqrtUp512 x := by
  simp only
  by_cases hxhi0 : x_hi = 0
  · -- x_hi = 0: use 256-bit ceiling sqrt bridge
    subst hxhi0
    simp only [Nat.zero_mul, Nat.zero_add]
    rw [osqrtUp_zero_fst, osqrtUp_zero_snd]
    simp only [Nat.zero_mul, Nat.zero_add]
    -- model_sqrt_up_evm x_lo satisfies ceiling sqrt spec
    have hspec := SqrtGeneratedModel.model_sqrt_up_evm_ceil_u256 x_lo hxlo
    -- sqrtUp512 x_lo also satisfies it (for x_lo < 2^256 < 2^512)
    have hx512 : x_lo < 2 ^ 512 := by
      calc x_lo < 2 ^ 256 := hxlo
        _ ≤ 2 ^ 512 := Nat.pow_le_pow_right (by omega) (by omega)
    -- Both satisfy the same uniqueness property
    exact sqrtUp512_unique x_lo (SqrtGeneratedModel.model_sqrt_up_evm x_lo) hx512
      hspec.1 hspec.2
  · -- x_hi > 0: floor sqrt + carry
    -- BLOCKED: (kernel) deep recursion when unfolding model_osqrtUp_evm.
    -- The auto-generated model inlines the 256-bit sqrtUp into the x_hi=0 branch,
    -- making the term too deep for the kernel even when only the else-branch is needed.
    -- Fix: refactor the generator to emit branches as separate named definitions.
    --
    -- Once unblocked, the proof chains:
    --   generalize model_sqrt512_evm → r, rw [mul512_high_word, mul512_low_word],
    --   generalize gt512 expr → needsUp, rw [add_with_carry],
    --   unfold sqrtUp512, rw [sqrt512_correct], case split on r*r < x.
    sorry

end Sqrt512Spec

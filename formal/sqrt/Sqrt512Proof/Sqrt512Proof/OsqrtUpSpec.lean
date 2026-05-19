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

/-- The generated model now folds `evmNot 0` to the literal `2^256 - 1`. -/
private theorem mul512_high_word_lit (r : Nat) (hr : r < WORD_MOD) :
    let mm := evmMulmod r r
      115792089237316195423570985008687907853269984665640564039457584007913129639935
    let m := evmMul r r
    evmSub (evmSub mm m) (evmLt mm m) = r * r / WORD_MOD := by
  have hword_pred :
      (115792089237316195423570985008687907853269984665640564039457584007913129639935 : Nat) =
      WORD_MOD - 1 := by
    unfold WORD_MOD
    omega
  simpa [hword_pred] using mul512_high_word r hr

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
    have hxhi_pos : 0 < x_hi := Nat.pos_of_ne_zero hxhi0
    -- Convert 2^256 to WORD_MOD for local use
    have hWM : WORD_MOD = 2 ^ 256 := rfl
    have hr_wm : x_hi < WORD_MOD := by rwa [hWM]
    have hlo_wm : x_lo < WORD_MOD := by rwa [hWM]
    -- Unfold model and simplify u256 on valid inputs
    unfold model_osqrtUp_evm
    have hxhi_u : u256 x_hi = x_hi := u256_id' x_hi hr_wm
    have hxlo_u : u256 x_lo = x_lo := u256_id' x_lo hlo_wm
    simp only [hxhi_u, hxlo_u]
    -- Evaluate evmEq x_hi 0 = 0 (since x_hi > 0)
    have hneq : evmEq x_hi 0 = 0 := by
      unfold evmEq; simp [u256_id' x_hi hr_wm]; exact Nat.ne_of_gt hxhi_pos
    -- Simplify: evmEq x_hi 0 = 0, then (0 ≠ 0) is decidably False, take else branches
    have h0eq0 : ¬((0 : Nat) ≠ 0) := by omega
    simp only [hneq]
    -- Abbreviate r = model_sqrt512_evm x_hi x_lo
    -- First establish r = natSqrt(x) and r < WORD_MOD
    have hr_eq : model_sqrt512_evm x_hi x_lo = natSqrt (x_hi * 2 ^ 256 + x_lo) :=
      model_sqrt512_evm_correct x_hi x_lo hxhi_pos hxhi hxlo
    -- natSqrt(x) < 2^256 because x < 2^512 so natSqrt(x) < 2^256
    have hx_lt : x_hi * 2 ^ 256 + x_lo < 2 ^ 512 := by
      calc x_hi * 2 ^ 256 + x_lo
          < 2 ^ 256 * 2 ^ 256 := by
            have := Nat.mul_lt_mul_of_pos_right hxhi (Nat.two_pow_pos 256)
            omega
        _ = 2 ^ 512 := by rw [← Nat.pow_add]
    have hnatSqrt_bound : natSqrt (x_hi * 2 ^ 256 + x_lo) < 2 ^ 256 := by
      suffices h : ¬(2 ^ 256 ≤ natSqrt (x_hi * 2 ^ 256 + x_lo)) by omega
      intro h
      have h2 := Nat.mul_le_mul h h
      have h3 := natSqrt_sq_le (x_hi * 2 ^ 256 + x_lo)
      have : 2 ^ 256 * 2 ^ 256 = 2 ^ 512 := by rw [← Nat.pow_add]
      omega
    have hr_wm' : model_sqrt512_evm x_hi x_lo < WORD_MOD := by
      rw [hr_eq, hWM]; exact hnatSqrt_bound
    -- Generalize model_sqrt512_evm x_hi x_lo = r
    generalize hgen : model_sqrt512_evm x_hi x_lo = r at *
    -- Rewrite sq_hi and sq_lo using mul512_high_word and mul512_low_word
    rw [mul512_high_word_lit r hr_wm', mul512_low_word r hr_wm']
    -- Establish bounds for sq_hi and sq_lo
    have hsqhi_bound : r * r / WORD_MOD < WORD_MOD := by
      have : r * r < WORD_MOD * WORD_MOD :=
        Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt hr_wm') hr_wm' (by unfold WORD_MOD; omega)
      exact Nat.div_lt_of_lt_mul this
    have hsqlo_bound : r * r % WORD_MOD < WORD_MOD := Nat.mod_lt _ (by unfold WORD_MOD; omega)
    -- Generalize the needsUp expression
    generalize hnu_def : evmOr (evmGt x_hi (r * r / WORD_MOD))
      (evmAnd (evmEq x_hi (r * r / WORD_MOD)) (evmGt x_lo (r * r % WORD_MOD))) = needsUp
    -- needsUp ∈ {0, 1}
    have hnu_01 : needsUp = 0 ∨ needsUp = 1 := by
      rw [← hnu_def]
      have hgt_01 : ∀ a b : Nat, a < WORD_MOD → b < WORD_MOD →
          evmGt a b = 0 ∨ evmGt a b = 1 := by
        intro a b ha hb; unfold evmGt
        simp only [u256_id' a ha, u256_id' b hb]; by_cases h : a > b <;> simp [h]
      have heq_01 : ∀ a b : Nat, a < WORD_MOD → b < WORD_MOD →
          evmEq a b = 0 ∨ evmEq a b = 1 := by
        intro a b ha hb; unfold evmEq
        simp only [u256_id' a ha, u256_id' b hb]; by_cases h : a = b <;> simp [h]
      have hand_01 : ∀ a b : Nat, (a = 0 ∨ a = 1) → (b = 0 ∨ b = 1) →
          evmAnd a b = 0 ∨ evmAnd a b = 1 := by
        intro a b ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
          (unfold evmAnd u256 WORD_MOD; simp (config := { decide := true }))
      have hor_01 : ∀ a b : Nat, (a = 0 ∨ a = 1) → (b = 0 ∨ b = 1) →
          evmOr a b = 0 ∨ evmOr a b = 1 := by
        intro a b ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
          (unfold evmOr u256 WORD_MOD; simp (config := { decide := true }))
      exact hor_01 _ _
        (hgt_01 x_hi (r * r / WORD_MOD) hr_wm hsqhi_bound)
        (hand_01 _ _
          (heq_01 x_hi (r * r / WORD_MOD) hr_wm hsqhi_bound)
          (hgt_01 x_lo (r * r % WORD_MOD) hlo_wm hsqlo_bound))
    -- Key semantic fact: needsUp ≠ 0 ↔ x_hi * W + x_lo > r * r
    have hnu_iff : (needsUp ≠ 0) ↔ (x_hi * WORD_MOD + x_lo > r * r) := by
      rw [← hnu_def]
      have h := gt512_correct x_hi x_lo (r * r / WORD_MOD) (r * r % WORD_MOD)
        hr_wm hlo_wm hsqhi_bound hsqlo_bound
      simp only at h
      -- h: (...) ↔ x_hi * WORD_MOD + x_lo > r*r/WORD_MOD * WORD_MOD + r*r % WORD_MOD
      -- Nat.div_add_mod gives WORD_MOD * (r*r / WORD_MOD) + ..., need to commute
      have hdm : r * r / WORD_MOD * WORD_MOD + r * r % WORD_MOD = r * r := by
        rw [Nat.mul_comm]; exact Nat.div_add_mod ..
      rw [hdm] at h; exact h
    -- Use add_with_carry
    have hcarry := add_with_carry r needsUp hr_wm' hnu_01
    simp only at hcarry
    -- evmAdd 0 x = x when x ∈ {0, 1}
    have heq00 : evmEq 0 0 = 1 := by
      unfold evmEq u256
      simp
    have heq00_nz : evmEq 0 0 ≠ 0 := by
      rw [heq00]
      decide
    simp [heq00_nz, ← hWM, hcarry]
    -- Goal: r + needsUp = sqrtUp512 (x_hi * WORD_MOD + x_lo)
    -- Rewrite hr_eq to use WORD_MOD
    have hr_eq_wm : r = natSqrt (x_hi * WORD_MOD + x_lo) := by rw [hr_eq, hWM]
    have hx_lt_wm : x_hi * WORD_MOD + x_lo < 2 ^ 512 := by rw [hWM]; exact hx_lt
    have hsqrt512_eq : sqrt512 (x_hi * WORD_MOD + x_lo) =
        natSqrt (x_hi * WORD_MOD + x_lo) :=
      sqrt512_correct (x_hi * WORD_MOD + x_lo) hx_lt_wm
    unfold sqrtUp512
    simp only
    rw [hsqrt512_eq, ← hr_eq_wm]
    -- Goal: r + needsUp = if r * r < x_hi * WORD_MOD + x_lo then r + 1 else r
    by_cases hlt : r * r < x_hi * WORD_MOD + x_lo
    · -- r*r < x: needsUp = 1
      simp only [hlt, ite_true]
      have hnu_nz : needsUp ≠ 0 := hnu_iff.mpr hlt
      rcases hnu_01 with h | h
      · exact absurd h hnu_nz
      · rw [h]
    · -- r*r ≥ x: needsUp = 0
      simp only [hlt, ite_false]
      have hnu_z : needsUp = 0 := by
        rcases hnu_01 with h | h
        · exact h
        · exfalso; have := hnu_iff.mp (by rw [h]; omega); omega
      rw [hnu_z]; omega

end Sqrt512Spec

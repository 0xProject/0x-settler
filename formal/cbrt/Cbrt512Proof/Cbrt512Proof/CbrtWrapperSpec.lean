/-
  Bridge proof: model_cbrt512_wrapper_evm computes icbrt.

  The auto-generated model_cbrt512_wrapper_evm dispatches:
    x_hi = 0 ⟹ inlined 256-bit floor cbrt (= model_cbrt_floor_evm from CbrtProof)
    x_hi > 0 ⟹ model_cbrt512_evm (within 1ulp) + cube-and-compare correction
-/
import Cbrt512Proof.GeneratedCbrt512Model
import Cbrt512Proof.GeneratedCbrt512Spec
import CbrtProof.GeneratedCbrtModel
import CbrtProof.GeneratedCbrtSpec
import CbrtProof.CbrtCorrect

namespace Cbrt512Spec

open Cbrt512GeneratedModel

-- ============================================================================
-- Section 1: Namespace compatibility
-- Both CbrtGeneratedModel and Cbrt512GeneratedModel define identical opcodes.
-- ============================================================================

section NamespaceCompat

theorem WORD_MOD_compat :
    @Cbrt512GeneratedModel.WORD_MOD = @CbrtGeneratedModel.WORD_MOD := rfl

theorem u256_compat (x : Nat) :
    Cbrt512GeneratedModel.u256 x = CbrtGeneratedModel.u256 x := by
  unfold Cbrt512GeneratedModel.u256 CbrtGeneratedModel.u256
  rw [WORD_MOD_compat]

theorem evmAdd_compat (a b : Nat) :
    Cbrt512GeneratedModel.evmAdd a b = CbrtGeneratedModel.evmAdd a b := by
  unfold Cbrt512GeneratedModel.evmAdd CbrtGeneratedModel.evmAdd
  simp [u256_compat]

theorem evmSub_compat (a b : Nat) :
    Cbrt512GeneratedModel.evmSub a b = CbrtGeneratedModel.evmSub a b := by
  unfold Cbrt512GeneratedModel.evmSub CbrtGeneratedModel.evmSub
  simp [u256_compat, WORD_MOD_compat]

theorem evmMul_compat (a b : Nat) :
    Cbrt512GeneratedModel.evmMul a b = CbrtGeneratedModel.evmMul a b := by
  unfold Cbrt512GeneratedModel.evmMul CbrtGeneratedModel.evmMul
  simp [u256_compat]

theorem evmDiv_compat (a b : Nat) :
    Cbrt512GeneratedModel.evmDiv a b = CbrtGeneratedModel.evmDiv a b := by
  unfold Cbrt512GeneratedModel.evmDiv CbrtGeneratedModel.evmDiv
  simp [u256_compat]

theorem evmShl_compat (s v : Nat) :
    Cbrt512GeneratedModel.evmShl s v = CbrtGeneratedModel.evmShl s v := by
  unfold Cbrt512GeneratedModel.evmShl CbrtGeneratedModel.evmShl
  simp [u256_compat]

theorem evmShr_compat (s v : Nat) :
    Cbrt512GeneratedModel.evmShr s v = CbrtGeneratedModel.evmShr s v := by
  unfold Cbrt512GeneratedModel.evmShr CbrtGeneratedModel.evmShr
  simp [u256_compat]

theorem evmClz_compat (v : Nat) :
    Cbrt512GeneratedModel.evmClz v = CbrtGeneratedModel.evmClz v := by
  unfold Cbrt512GeneratedModel.evmClz CbrtGeneratedModel.evmClz
  simp [u256_compat]

theorem evmLt_compat (a b : Nat) :
    Cbrt512GeneratedModel.evmLt a b = CbrtGeneratedModel.evmLt a b := by
  unfold Cbrt512GeneratedModel.evmLt CbrtGeneratedModel.evmLt
  simp [u256_compat]

theorem evmGt_compat (a b : Nat) :
    Cbrt512GeneratedModel.evmGt a b = CbrtGeneratedModel.evmGt a b := by
  unfold Cbrt512GeneratedModel.evmGt CbrtGeneratedModel.evmGt
  simp [u256_compat]

theorem evmEq_compat (a b : Nat) :
    Cbrt512GeneratedModel.evmEq a b = CbrtGeneratedModel.evmEq a b := by
  unfold Cbrt512GeneratedModel.evmEq CbrtGeneratedModel.evmEq
  simp [u256_compat]

theorem evmNot_compat (a : Nat) :
    Cbrt512GeneratedModel.evmNot a = CbrtGeneratedModel.evmNot a := by
  unfold Cbrt512GeneratedModel.evmNot CbrtGeneratedModel.evmNot
  simp [u256_compat, WORD_MOD_compat]

theorem evmMulmod_compat (a b n : Nat) :
    Cbrt512GeneratedModel.evmMulmod a b n = CbrtGeneratedModel.evmMulmod a b n := by
  unfold Cbrt512GeneratedModel.evmMulmod CbrtGeneratedModel.evmMulmod
  simp [u256_compat]

theorem evmOr_compat (a b : Nat) :
    Cbrt512GeneratedModel.evmOr a b = CbrtGeneratedModel.evmOr a b := by
  unfold Cbrt512GeneratedModel.evmOr CbrtGeneratedModel.evmOr
  simp [u256_compat]

theorem evmAnd_compat (a b : Nat) :
    Cbrt512GeneratedModel.evmAnd a b = CbrtGeneratedModel.evmAnd a b := by
  unfold Cbrt512GeneratedModel.evmAnd CbrtGeneratedModel.evmAnd
  simp [u256_compat]

end NamespaceCompat

-- ============================================================================
-- Section 2: u256 idempotence
-- ============================================================================

/-- u256 is idempotent: u256(u256(x)) = u256(x). -/
theorem u256_idem (x : Nat) :
    Cbrt512GeneratedModel.u256 (Cbrt512GeneratedModel.u256 x) = Cbrt512GeneratedModel.u256 x := by
  unfold Cbrt512GeneratedModel.u256 Cbrt512GeneratedModel.WORD_MOD
  exact Nat.mod_eq_of_lt (Nat.mod_lt x (Nat.two_pow_pos 256))

theorem cu256_idem (x : Nat) :
    CbrtGeneratedModel.u256 (CbrtGeneratedModel.u256 x) = CbrtGeneratedModel.u256 x := by
  unfold CbrtGeneratedModel.u256 CbrtGeneratedModel.WORD_MOD
  exact Nat.mod_eq_of_lt (Nat.mod_lt x (Nat.two_pow_pos 256))

theorem cu256_zero : CbrtGeneratedModel.u256 0 = 0 := by
  unfold CbrtGeneratedModel.u256 CbrtGeneratedModel.WORD_MOD; simp

-- ============================================================================
-- Section 3: The wrapper's x_hi=0 branch equals model_cbrt_floor_evm
-- ============================================================================

/-- When x_hi = 0, model_cbrt512_wrapper_evm calls model_cbrt256_floor_evm,
    which is identical (modulo namespace) to model_cbrt_floor_evm from CbrtProof. -/
theorem wrapper_zero_eq_cbrt_floor_evm (x_lo : Nat) :
    model_cbrt512_wrapper_evm 0 x_lo = CbrtGeneratedModel.model_cbrt_floor_evm x_lo := by
  -- Unfold all model definitions to expose the full EVM expression
  simp only [model_cbrt512_wrapper_evm, model_cbrt256_floor_evm,
    CbrtGeneratedModel.model_cbrt_floor_evm, CbrtGeneratedModel.model_cbrt_evm]
  -- Convert Cbrt512 namespace ops to CbrtGeneratedModel ops
  simp only [evmEq_compat, evmShr_compat, evmAdd_compat, evmDiv_compat,
    evmSub_compat, evmClz_compat, evmShl_compat, evmLt_compat,
    evmMul_compat, evmGt_compat, u256_compat]
  -- Simplify: u256(u256(x)) = u256(x) and u256(0) = 0
  simp only [cu256_zero, cu256_idem]
  -- Simplify the conditional: evmEq 0 0 evaluates to 1, etc.
  simp (config := { decide := true })

-- ============================================================================
-- Section 4: icbrt uniqueness bridge
-- ============================================================================

/-- The integer cube root is unique: restatement for local use. -/
theorem icbrt_unique (n r : Nat) (hlo : r * r * r ≤ n) (hhi : n < (r + 1) * (r + 1) * (r + 1)) :
    r = icbrt n :=
  icbrt_eq_of_bounds n r hlo hhi

-- ============================================================================
-- Section 5: Helper lemmas for x_hi > 0 — mul512 correctness
-- ============================================================================

/-- Generalized high word: mulmod(a,b,2^256-1) combined with mul(a,b) and sub/lt
    recovers (a*b)/2^256. -/
theorem mul512_high_word_general (a b : Nat) (ha : a < WORD_MOD) (hb : b < WORD_MOD) :
    let mm := evmMulmod a b (evmNot 0)
    let m := evmMul a b
    evmSub (evmSub mm m) (evmLt mm m) = a * b / WORD_MOD := by
  simp only
  have hNot0 : evmNot 0 = WORD_MOD - 1 := by
    unfold evmNot u256 WORD_MOD; simp
  have hWM1_pos : (0 : Nat) < WORD_MOD - 1 := by unfold WORD_MOD; omega
  have hWM1_lt : WORD_MOD - 1 < WORD_MOD := by unfold WORD_MOD; omega
  have hmm : evmMulmod a b (evmNot 0) = (a * b) % (WORD_MOD - 1) := by
    unfold evmMulmod
    simp only [u256_id' a ha, hNot0, u256_id' (WORD_MOD - 1) hWM1_lt, u256_id' b hb]
    simp [Nat.ne_of_gt hWM1_pos]
  have hm : evmMul a b = (a * b) % WORD_MOD := by
    unfold evmMul u256; simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  rw [hmm, hm]
  have hq_bound : a * b / WORD_MOD < WORD_MOD := by
    have : a * b < WORD_MOD * WORD_MOD :=
      Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt ha) hb (by unfold WORD_MOD; omega)
    exact Nat.div_lt_of_lt_mul this
  have hlo_bound : a * b % WORD_MOD < WORD_MOD := Nat.mod_lt _ (by unfold WORD_MOD; omega)
  have hdecomp : a * b = a * b / WORD_MOD * WORD_MOD + a * b % WORD_MOD := by
    have := Nat.div_add_mod (a * b) WORD_MOD
    rw [Nat.mul_comm] at this; omega
  have hhi_eq : (a * b) % (WORD_MOD - 1) = (a * b / WORD_MOD + a * b % WORD_MOD) % (WORD_MOD - 1) := by
    have hqW : a * b / WORD_MOD * WORD_MOD =
        (WORD_MOD - 1) * (a * b / WORD_MOD) + a * b / WORD_MOD := by
      have hsc := Nat.sub_add_cancel (Nat.one_le_of_lt (show 1 < WORD_MOD from by unfold WORD_MOD; omega))
      have h := Nat.mul_add (a * b / WORD_MOD) (WORD_MOD - 1) 1
      rw [hsc, Nat.mul_one] at h
      rw [h, Nat.mul_comm (a * b / WORD_MOD) (WORD_MOD - 1)]
    have hab_eq : a * b = (WORD_MOD - 1) * (a * b / WORD_MOD) + (a * b / WORD_MOD + a * b % WORD_MOD) := by
      omega
    have step := Nat.mul_add_mod (WORD_MOD - 1) (a * b / WORD_MOD) (a * b / WORD_MOD + a * b % WORD_MOD)
    rw [← hab_eq] at step; exact step
  have hhi_bound : (a * b) % (WORD_MOD - 1) < WORD_MOD - 1 := Nat.mod_lt _ hWM1_pos
  by_cases hcase : a * b / WORD_MOD + a * b % WORD_MOD < WORD_MOD - 1
  · have hhi_val : (a * b) % (WORD_MOD - 1) = a * b / WORD_MOD + a * b % WORD_MOD := by
      rw [hhi_eq, Nat.mod_eq_of_lt hcase]
    have hhi_wm : (a * b) % (WORD_MOD - 1) < WORD_MOD := by omega
    have hge : a * b % WORD_MOD ≤ (a * b) % (WORD_MOD - 1) := by
      rw [hhi_val]; exact Nat.le_add_left _ _
    have hlt_eq : evmLt ((a * b) % (WORD_MOD - 1)) (a * b % WORD_MOD) = 0 := by
      unfold evmLt u256
      simp only [Nat.mod_eq_of_lt hhi_wm, Nat.mod_eq_of_lt hlo_bound]
      exact if_neg (Nat.not_lt.mpr hge)
    rw [hlt_eq]
    have hsub1 : evmSub ((a * b) % (WORD_MOD - 1)) (a * b % WORD_MOD) =
        (a * b) % (WORD_MOD - 1) - a * b % WORD_MOD :=
      evmSub_eq_of_le _ _ hhi_wm hge
    rw [hsub1]
    have hq_eq : (a * b) % (WORD_MOD - 1) - a * b % WORD_MOD = a * b / WORD_MOD := by
      omega
    rw [hq_eq]
    exact evmSub_eq_of_le _ 0 hq_bound (Nat.zero_le _)
  · have hcase' : WORD_MOD - 1 ≤ a * b / WORD_MOD + a * b % WORD_MOD := Nat.not_lt.mp hcase
    have hq_le : a * b / WORD_MOD ≤ WORD_MOD - 2 := by
      have ha' : a ≤ WORD_MOD - 1 := by omega
      have hb' : b ≤ WORD_MOD - 1 := by omega
      have hab : a * b ≤ (WORD_MOD - 1) * (WORD_MOD - 1) := Nat.mul_le_mul ha' hb'
      have h1 : a * b / WORD_MOD ≤ (WORD_MOD - 1) * (WORD_MOD - 1) / WORD_MOD :=
        @Nat.div_le_div_right _ _ WORD_MOD hab
      suffices h : (WORD_MOD - 1) * (WORD_MOD - 1) / WORD_MOD = WORD_MOD - 2 by omega
      unfold WORD_MOD; omega
    have hql_lt : a * b / WORD_MOD + a * b % WORD_MOD < 2 * (WORD_MOD - 1) := by omega
    have hhi_val : (a * b) % (WORD_MOD - 1) =
        a * b / WORD_MOD + a * b % WORD_MOD - (WORD_MOD - 1) := by
      rw [hhi_eq,
          Nat.mod_eq_sub_mod hcase',
          Nat.mod_eq_of_lt (by omega)]
    have hlt_lo : (a * b) % (WORD_MOD - 1) < a * b % WORD_MOD := by
      rw [hhi_val]; omega
    have hhi_wm : (a * b) % (WORD_MOD - 1) < WORD_MOD := by omega
    have hlt_eq : evmLt ((a * b) % (WORD_MOD - 1)) (a * b % WORD_MOD) = 1 := by
      unfold evmLt u256
      simp [Nat.mod_eq_of_lt hhi_wm, Nat.mod_eq_of_lt hlo_bound]
      exact hlt_lo
    rw [hlt_eq]
    have hsub1 : evmSub ((a * b) % (WORD_MOD - 1)) (a * b % WORD_MOD) =
        (a * b) % (WORD_MOD - 1) + WORD_MOD - a * b % WORD_MOD := by
      unfold evmSub u256
      simp [Nat.mod_eq_of_lt hhi_wm, Nat.mod_eq_of_lt hlo_bound]
      exact Nat.mod_eq_of_lt (show (a * b) % (WORD_MOD - 1) + WORD_MOD - a * b % WORD_MOD < WORD_MOD
        by rw [hhi_val]; omega)
    rw [hsub1]
    have hval : (a * b) % (WORD_MOD - 1) + WORD_MOD - a * b % WORD_MOD < WORD_MOD := by
      rw [hhi_val]; omega
    have hsub2 : evmSub ((a * b) % (WORD_MOD - 1) + WORD_MOD - a * b % WORD_MOD) 1 =
        (a * b) % (WORD_MOD - 1) + WORD_MOD - a * b % WORD_MOD - 1 :=
      evmSub_eq_of_le _ 1 hval (by rw [hhi_val]; omega)
    rw [hsub2]
    rw [hhi_val]; omega

/-- mul(a, b) gives the low word of a*b. -/
theorem mul512_low_word_general (a b : Nat) (ha : a < WORD_MOD) (hb : b < WORD_MOD) :
    evmMul a b = (a * b) % WORD_MOD := by
  unfold evmMul u256; simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

/-- mulmod(r, r, 2^256-1) combined with mul(r,r) and sub/lt recovers r²/2^256.
    Special case of mul512_high_word_general with a = b = r. -/
theorem mul512_high_word (r : Nat) (hr : r < WORD_MOD) :
    let mm := evmMulmod r r (evmNot 0)
    let m := evmMul r r
    evmSub (evmSub mm m) (evmLt mm m) = r * r / WORD_MOD :=
  mul512_high_word_general r r hr hr

/-- mul(r, r) gives the low word of r². -/
theorem mul512_low_word (r : Nat) (hr : r < WORD_MOD) :
    evmMul r r = r * r % WORD_MOD :=
  mul512_low_word_general r r hr hr

-- ============================================================================
-- Section 6: 512×256 multiplication for cubing
-- ============================================================================

/-- Helper: (a/k)*b ≤ (a*b)/k for natural numbers. -/
private theorem div_mul_le_mul_div (a b k : Nat) (hk : 0 < k) : a / k * b ≤ a * b / k := by
  -- Strategy: a/k*b*k ≤ a*b, then divide both sides by k
  have h1 : a / k * b * k ≤ a * b := by
    calc a / k * b * k
        = a / k * k * b := by rw [Nat.mul_assoc, Nat.mul_comm b k, ← Nat.mul_assoc]
      _ ≤ a * b := Nat.mul_le_mul_right b (Nat.div_mul_le_self a k)
  have h2 : a / k * b * k / k = a / k * b :=
    Nat.mul_div_cancel (a / k * b) hk
  calc a / k * b
      = a / k * b * k / k := h2.symm
    _ ≤ a * b / k := Nat.div_le_div_right h1

/-- Cubing via mulmod: given r < 2^256 with r³ < 2^512, compute (r²_hi, r²_lo)
    then multiply by r to get (r³_hi, r³_lo) where r³_hi * 2^256 + r³_lo = r³.
    This mirrors the cube-and-compare assembly in 512Math.sol's `cbrt` / `cbrtUp`
    wrappers.
    The hypothesis hcube ensures the evmAdd does not overflow. -/
theorem cube512_correct (r : Nat) (hr : r < WORD_MOD) (hcube : r * r * r < WORD_MOD * WORD_MOD) :
    let mm1 := evmMulmod r r (evmNot 0)
    let r2_lo := evmMul r r
    let r2_hi := evmSub (evmSub mm1 r2_lo) (evmLt mm1 r2_lo)
    let mm2 := evmMulmod r2_lo r (evmNot 0)
    let r3_lo := evmMul r2_lo r
    let r3_hi := evmAdd (evmSub (evmSub mm2 r3_lo) (evmLt mm2 r3_lo)) (evmMul r2_hi r)
    r3_hi * WORD_MOD + r3_lo = r * r * r := by
  simp only
  have hWpos : (0 : Nat) < WORD_MOD := by unfold WORD_MOD; omega
  -- Abbreviations: P = r²%W, Q = r²/W
  -- Euclidean decomposition of r²: Q*W + P = r² (i.e., r*r = Q*W + P)
  -- Then r³ = r²*r = (Q*W + P)*r = Q*r*W + P*r
  -- And P*r = (P*r/W)*W + P*r%W
  -- So r³ = (P*r/W + Q*r)*W + P*r%W

  -- Step 1: Squaring — establish r2_hi = Q, r2_lo = P
  have h_r2_hi : evmSub (evmSub (evmMulmod r r (evmNot 0)) (evmMul r r))
      (evmLt (evmMulmod r r (evmNot 0)) (evmMul r r)) = r * r / WORD_MOD :=
    mul512_high_word r hr
  have h_r2_lo : evmMul r r = (r * r) % WORD_MOD :=
    mul512_low_word r hr
  -- Rewrite: first r2_hi (compound, contains evmMul r r), then standalone evmMul r r
  rw [h_r2_hi, h_r2_lo]

  -- Step 2: Cubing step — high and low words of P*r
  have hP_lt : (r * r) % WORD_MOD < WORD_MOD := Nat.mod_lt _ hWpos
  have h_cube_hi :
      evmSub (evmSub (evmMulmod ((r * r) % WORD_MOD) r (evmNot 0)) (evmMul ((r * r) % WORD_MOD) r))
        (evmLt (evmMulmod ((r * r) % WORD_MOD) r (evmNot 0)) (evmMul ((r * r) % WORD_MOD) r))
      = (r * r) % WORD_MOD * r / WORD_MOD :=
    mul512_high_word_general ((r * r) % WORD_MOD) r hP_lt hr
  have h_r3_lo : evmMul ((r * r) % WORD_MOD) r = ((r * r) % WORD_MOD * r) % WORD_MOD :=
    mul512_low_word_general ((r * r) % WORD_MOD) r hP_lt hr
  rw [h_cube_hi, h_r3_lo]

  -- Step 3: Bounds for cross term Q*r
  have hQ_lt : r * r / WORD_MOD < WORD_MOD :=
    Nat.div_lt_of_lt_mul (Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt hr) hr
      (by unfold WORD_MOD; omega))
  have hQr_lt : r * r / WORD_MOD * r < WORD_MOD := by
    calc r * r / WORD_MOD * r
        ≤ r * r * r / WORD_MOD := div_mul_le_mul_div (r * r) r WORD_MOD hWpos
      _ < WORD_MOD := Nat.div_lt_of_lt_mul hcube

  -- Step 4: evmMul Q r = Q*r (no overflow)
  have hevmMul_hi : evmMul (r * r / WORD_MOD) r = r * r / WORD_MOD * r := by
    unfold evmMul u256
    simp [Nat.mod_eq_of_lt hQ_lt, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hQr_lt]
  rw [hevmMul_hi]

  -- Step 5: evmAdd doesn't overflow — the sum P*r/W + Q*r = r³/W < W
  -- Key decomposition: r³ = Q*r*W + P*r (multiply Euclidean decomp of r² by r)
  have h_r3_decomp : r * r * r = r * r / WORD_MOD * r * WORD_MOD + (r * r) % WORD_MOD * r := by
    have h_eucl := Nat.div_add_mod (r * r) WORD_MOD
    -- h_eucl: WORD_MOD * (r*r/W) + r*r%W = r*r
    -- Multiply by r using congruence: (Q*W + P)*r = Q*W*r + P*r = Q*r*W + P*r
    calc r * r * r
        = (WORD_MOD * (r * r / WORD_MOD) + (r * r) % WORD_MOD) * r :=
          congrArg (· * r) h_eucl.symm
      _ = WORD_MOD * (r * r / WORD_MOD) * r + (r * r) % WORD_MOD * r := Nat.add_mul _ _ r
      _ = r * r / WORD_MOD * WORD_MOD * r + (r * r) % WORD_MOD * r := by
          rw [Nat.mul_comm WORD_MOD (r * r / WORD_MOD)]
      _ = r * r / WORD_MOD * r * WORD_MOD + (r * r) % WORD_MOD * r := by
          rw [Nat.mul_assoc, Nat.mul_comm WORD_MOD r, ← Nat.mul_assoc]
  -- From r³ = Q*r*W + P*r, we get r³/W = Q*r + P*r/W
  have h_sum_eq : (r * r) % WORD_MOD * r / WORD_MOD + r * r / WORD_MOD * r
      = r * r * r / WORD_MOD := by
    rw [h_r3_decomp]
    rw [show r * r / WORD_MOD * r * WORD_MOD + (r * r) % WORD_MOD * r
        = (r * r) % WORD_MOD * r + r * r / WORD_MOD * r * WORD_MOD from by omega]
    exact (Nat.add_mul_div_right ((r * r) % WORD_MOD * r) (r * r / WORD_MOD * r) hWpos).symm
  have h_sum_lt : (r * r) % WORD_MOD * r / WORD_MOD + r * r / WORD_MOD * r < WORD_MOD := by
    rw [h_sum_eq]; exact Nat.div_lt_of_lt_mul hcube

  have hevmAdd : evmAdd ((r * r) % WORD_MOD * r / WORD_MOD) (r * r / WORD_MOD * r)
      = (r * r) % WORD_MOD * r / WORD_MOD + r * r / WORD_MOD * r := by
    exact evmAdd_eq' _ _ (by omega) hQr_lt h_sum_lt
  rw [hevmAdd]

  -- Step 6: Final algebra
  -- Goal: ((r*r)%W*r/W + r*r/W*r) * W + ((r*r)%W*r)%W = r*r*r
  -- We prove it equals r³ by reversing the decomposition chain.
  have h_Pr_eucl := Nat.div_add_mod ((r * r) % WORD_MOD * r) WORD_MOD
  -- h_Pr_eucl: W * (P*r/W) + P*r%W = P*r
  symm
  calc r * r * r
      = r * r / WORD_MOD * r * WORD_MOD + (r * r) % WORD_MOD * r := h_r3_decomp
    _ = r * r / WORD_MOD * r * WORD_MOD
        + (WORD_MOD * ((r * r) % WORD_MOD * r / WORD_MOD) + (r * r) % WORD_MOD * r % WORD_MOD) := by
        rw [h_Pr_eucl]
    _ = (r * r) % WORD_MOD * r / WORD_MOD * WORD_MOD + r * r / WORD_MOD * r * WORD_MOD
        + (r * r) % WORD_MOD * r % WORD_MOD := by
        rw [Nat.mul_comm WORD_MOD ((r * r) % WORD_MOD * r / WORD_MOD)]; omega
    _ = ((r * r) % WORD_MOD * r / WORD_MOD + r * r / WORD_MOD * r) * WORD_MOD
        + (r * r) % WORD_MOD * r % WORD_MOD := by rw [← Nat.add_mul]

-- ============================================================================
-- Section 7: 512-bit lexicographic comparison for cube-and-compare
-- ============================================================================

/-- The 512-bit lexicographic comparison correctly computes x > r³. -/
theorem gt512_correct (x_hi x_lo sq_hi sq_lo : Nat)
    (hxhi : x_hi < WORD_MOD) (hxlo : x_lo < WORD_MOD)
    (hsqhi : sq_hi < WORD_MOD) (hsqlo : sq_lo < WORD_MOD) :
    let cmp := evmOr (evmGt sq_hi x_hi)
      (evmAnd (evmEq sq_hi x_hi) (evmGt sq_lo x_lo))
    (cmp ≠ 0) ↔ (sq_hi * WORD_MOD + sq_lo > x_hi * WORD_MOD + x_lo) := by
  simp only
  have hgt_hi : evmGt sq_hi x_hi = if sq_hi > x_hi then 1 else 0 := by
    unfold evmGt u256; simp [Nat.mod_eq_of_lt hsqhi, Nat.mod_eq_of_lt hxhi]
  have heq_hi : evmEq sq_hi x_hi = if sq_hi = x_hi then 1 else 0 := by
    unfold evmEq u256; simp [Nat.mod_eq_of_lt hsqhi, Nat.mod_eq_of_lt hxhi]
  have hgt_lo : evmGt sq_lo x_lo = if sq_lo > x_lo then 1 else 0 := by
    unfold evmGt u256; simp [Nat.mod_eq_of_lt hsqlo, Nat.mod_eq_of_lt hxlo]
  rw [hgt_hi, heq_hi, hgt_lo]
  by_cases hgt : sq_hi > x_hi
  · have hneq : ¬(sq_hi = x_hi) := by omega
    simp only [hgt, ite_true, hneq, ite_false]
    have hor_nz : ∀ v, evmOr 1 (evmAnd 0 v) ≠ 0 := by
      intro v; unfold evmOr evmAnd u256 WORD_MOD; simp (config := { decide := true })
    constructor
    · intro _
      have h1 : x_hi * WORD_MOD + WORD_MOD ≤ sq_hi * WORD_MOD := by
        have := Nat.mul_le_mul_right WORD_MOD hgt
        rwa [Nat.succ_mul] at this
      omega
    · intro _; exact hor_nz _
  · by_cases heq : sq_hi = x_hi
    · subst heq
      simp only [Nat.lt_irrefl, ite_false, ite_true]
      by_cases hgtlo : sq_lo > x_lo
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
    · have hlt : sq_hi < x_hi := by omega
      have hng : ¬(sq_hi > x_hi) := by omega
      simp only [hng, ite_false, heq, ite_false]
      have hor_z : ∀ v, evmOr 0 (evmAnd 0 v) = 0 := by
        intro v; unfold evmOr evmAnd u256 WORD_MOD; simp (config := { decide := true })
      constructor
      · intro h; exact absurd (hor_z _) h
      · intro h
        have h1 : sq_hi * WORD_MOD + WORD_MOD ≤ x_hi * WORD_MOD := by
          have := Nat.mul_le_mul_right WORD_MOD hlt
          rwa [Nat.succ_mul] at this
        omega

-- ============================================================================
-- Section 7b: Helper lemmas for cube-and-compare correction
-- ============================================================================

/-- Any evmMul result is < WORD_MOD (it's a mod operation). -/
private theorem evmMul_lt_WORD_MOD (a b : Nat) : evmMul a b < WORD_MOD := by
  unfold evmMul u256 WORD_MOD; exact Nat.mod_lt _ (Nat.two_pow_pos 256)

/-- Any evmAdd result is < WORD_MOD (it's a mod operation). -/
private theorem evmAdd_lt_WORD_MOD (a b : Nat) : evmAdd a b < WORD_MOD := by
  unfold evmAdd u256 WORD_MOD; exact Nat.mod_lt _ (Nat.two_pow_pos 256)

/-- evmGt returns 0 or 1. -/
theorem evmGt_01 (a b : Nat) (ha : a < WORD_MOD) (hb : b < WORD_MOD) :
    evmGt a b = 0 ∨ evmGt a b = 1 := by
  rw [evmGt_eq' a b ha hb]; split <;> simp

/-- evmEq returns 0 or 1. -/
theorem evmEq_01 (a b : Nat) (ha : a < WORD_MOD) (hb : b < WORD_MOD) :
    evmEq a b = 0 ∨ evmEq a b = 1 := by
  rw [evmEq_eq' a b ha hb]; split <;> simp

/-- evmLt returns 0 or 1. -/
theorem evmLt_01 (a b : Nat) (ha : a < WORD_MOD) (hb : b < WORD_MOD) :
    evmLt a b = 0 ∨ evmLt a b = 1 := by
  rw [evmLt_eq' a b ha hb]; split <;> simp

/-- evmAnd of 0/1 values returns 0 or 1. -/
theorem evmAnd_01 (a b : Nat) (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    evmAnd a b = 0 ∨ evmAnd a b = 1 := by
  have haw : a < WORD_MOD := by rcases ha with rfl | rfl <;> (unfold WORD_MOD; omega)
  have hbw : b < WORD_MOD := by rcases hb with rfl | rfl <;> (unfold WORD_MOD; omega)
  rw [evmAnd_eq' a b haw hbw]
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp

/-- evmOr of 0/1 values returns 0 or 1. -/
theorem evmOr_01 (a b : Nat) (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    evmOr a b = 0 ∨ evmOr a b = 1 := by
  have haw : a < WORD_MOD := by rcases ha with rfl | rfl <;> (unfold WORD_MOD; omega)
  have hbw : b < WORD_MOD := by rcases hb with rfl | rfl <;> (unfold WORD_MOD; omega)
  rw [evmOr_eq' a b haw hbw]
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp

/-- The 512-bit gt comparison produces 0 or 1. -/
private theorem gt512_01 (x_hi x_lo sq_hi sq_lo : Nat)
    (hxhi : x_hi < WORD_MOD) (hxlo : x_lo < WORD_MOD)
    (hsqhi : sq_hi < WORD_MOD) (hsqlo : sq_lo < WORD_MOD) :
    let cmp := evmOr (evmGt sq_hi x_hi) (evmAnd (evmEq sq_hi x_hi) (evmGt sq_lo x_lo))
    cmp = 0 ∨ cmp = 1 :=
  evmOr_01 _ _ (evmGt_01 _ _ hsqhi hxhi) (evmAnd_01 _ _ (evmEq_01 _ _ hsqhi hxhi) (evmGt_01 _ _ hsqlo hxlo))

/-- The 512-bit lt comparison correctly computes sq < x. -/
theorem lt512_correct (x_hi x_lo sq_hi sq_lo : Nat)
    (hxhi : x_hi < WORD_MOD) (hxlo : x_lo < WORD_MOD)
    (hsqhi : sq_hi < WORD_MOD) (hsqlo : sq_lo < WORD_MOD) :
    let cmp := evmOr (evmLt sq_hi x_hi)
      (evmAnd (evmEq sq_hi x_hi) (evmLt sq_lo x_lo))
    (cmp ≠ 0) ↔ (sq_hi * WORD_MOD + sq_lo < x_hi * WORD_MOD + x_lo) := by
  simp only
  -- evmLt a b = evmGt b a, evmEq a b = evmEq b a
  have hlt_hi : evmLt sq_hi x_hi = evmGt x_hi sq_hi := by
    rw [evmLt_eq' sq_hi x_hi hsqhi hxhi, evmGt_eq' x_hi sq_hi hxhi hsqhi]
  have heq_comm : evmEq sq_hi x_hi = evmEq x_hi sq_hi := by
    rw [evmEq_eq' sq_hi x_hi hsqhi hxhi, evmEq_eq' x_hi sq_hi hxhi hsqhi]
    by_cases h : sq_hi = x_hi
    · simp [h]
    · simp [h, show x_hi ≠ sq_hi from Ne.symm h]
  have hlt_lo : evmLt sq_lo x_lo = evmGt x_lo sq_lo := by
    rw [evmLt_eq' sq_lo x_lo hsqlo hxlo, evmGt_eq' x_lo sq_lo hxlo hsqlo]
  rw [hlt_hi, heq_comm, hlt_lo]
  -- Now matches gt512_correct with swapped roles
  have hgt := gt512_correct sq_hi sq_lo x_hi x_lo hsqhi hsqlo hxhi hxlo
  simp only at hgt
  exact hgt

/-- The 512-bit lt comparison produces 0 or 1. -/
private theorem lt512_01 (x_hi x_lo sq_hi sq_lo : Nat)
    (hxhi : x_hi < WORD_MOD) (hxlo : x_lo < WORD_MOD)
    (hsqhi : sq_hi < WORD_MOD) (hsqlo : sq_lo < WORD_MOD) :
    let cmp := evmOr (evmLt sq_hi x_hi) (evmAnd (evmEq sq_hi x_hi) (evmLt sq_lo x_lo))
    cmp = 0 ∨ cmp = 1 :=
  evmOr_01 _ _ (evmLt_01 _ _ hsqhi hxhi) (evmAnd_01 _ _ (evmEq_01 _ _ hsqhi hxhi) (evmLt_01 _ _ hsqlo hxlo))

-- ============================================================================
-- Section 8: Main theorem — model_cbrt512_wrapper_evm = icbrt
-- ============================================================================

set_option exponentiation.threshold 512 in
/-- The EVM model of the cbrt(uint512) wrapper computes icbrt. -/
theorem model_cbrt512_wrapper_evm_correct (x_hi x_lo : Nat)
    (hxhi : x_hi < 2 ^ 256) (hxlo : x_lo < 2 ^ 256) :
    model_cbrt512_wrapper_evm x_hi x_lo = icbrt (x_hi * 2 ^ 256 + x_lo) := by
  by_cases hxhi0 : x_hi = 0
  · -- x_hi = 0: the wrapper uses the inlined 256-bit floor cbrt
    subst hxhi0
    simp only [Nat.zero_mul, Nat.zero_add]
    -- Step 1: wrapper's x_hi=0 branch = model_cbrt_floor_evm x_lo
    rw [wrapper_zero_eq_cbrt_floor_evm x_lo]
    -- Step 2: model_cbrt_floor_evm = icbrt (from CbrtProof)
    -- model_cbrt_floor_evm_correct requires 0 < x, handle x_lo = 0 separately
    by_cases hxlo0 : x_lo = 0
    · -- x_lo = 0: model_cbrt_floor_evm 0 = 0 = icbrt 0
      subst hxlo0
      -- model_cbrt_floor_evm 0 = floorCbrt 0
      rw [CbrtGeneratedModel.model_cbrt_floor_evm_eq_floorCbrt 0 hxlo]
      -- floorCbrt 0 = 0 = icbrt 0
      unfold floorCbrt innerCbrt cbrtSeed cbrtStep
      simp [icbrt, icbrtAux]
    · exact CbrtGeneratedModel.model_cbrt_floor_evm_correct x_lo (Nat.pos_of_ne_zero hxlo0) hxlo
  · -- x_hi > 0: model_cbrt512_evm within 1ulp + cube-and-compare correction
    have hxhi_pos : 0 < x_hi := Nat.pos_of_ne_zero hxhi0
    have hxhi_wm : x_hi < WORD_MOD := by unfold WORD_MOD; exact hxhi
    have hxlo_wm : x_lo < WORD_MOD := by unfold WORD_MOD; exact hxlo
    -- Unfold wrapper and simplify u256
    unfold model_cbrt512_wrapper_evm
    simp only [u256_id' x_hi hxhi_wm, u256_id' x_lo hxlo_wm]
    -- Eliminate conditional: evmEq x_hi 0 = 0 since x_hi > 0
    have hneq : evmEq x_hi 0 = 0 := by
      rw [evmEq_eq' x_hi 0 hxhi_wm (by unfold WORD_MOD; omega)]
      exact if_neg (Nat.ne_of_gt hxhi_pos)
    have hcond_neg : ¬((evmEq x_hi 0) ≠ 0) := by rw [hneq]; omega
    rw [if_neg hcond_neg]
    -- Generalize the approximation: replace model_cbrt512_evm x_hi x_lo with r
    generalize hr_def : model_cbrt512_evm x_hi x_lo = r
    -- Name cube sub-expressions via let (matching cube512_correct's structure)
    let r2lo := evmMul r r
    let mm1 := evmMulmod r r (evmNot 0)
    let r2hi := evmSub (evmSub mm1 r2lo) (evmLt mm1 r2lo)
    let mm2 := evmMulmod r2lo r (evmNot 0)
    let r3lo := evmMul r2lo r
    let r3hi := evmAdd (evmSub (evmSub mm2 r3lo) (evmLt mm2 r3lo)) (evmMul r2hi r)
    let cmp := evmOr (evmGt r3hi x_hi) (evmAnd (evmEq r3hi x_hi) (evmGt r3lo x_lo))
    -- Restate goal using named variables (definitional equality)
    show evmSub r cmp = icbrt (x_hi * 2 ^ 256 + x_lo)
    -- Get bounds from strengthened within_1ulp theorem
    have hbounds := model_cbrt512_evm_within_1ulp x_hi x_lo hxhi_pos
      (show x_hi < 2 ^ 256 from hxhi) (show x_lo < 2 ^ 256 from hxlo)
    simp only at hbounds
    rw [hr_def] at hbounds
    obtain ⟨h_lo, h_hi, hr_lt, hcube_lt, _⟩ := hbounds
    -- Cube decomposition: r3hi * WORD_MOD + r3lo = r³
    have hcube_eq : r3hi * WORD_MOD + r3lo = r * r * r := cube512_correct r hr_lt hcube_lt
    -- Bounds on r3hi and r3lo
    have hr3lo_lt : r3lo < WORD_MOD := evmMul_lt_WORD_MOD _ _
    have hr3hi_lt : r3hi < WORD_MOD := evmAdd_lt_WORD_MOD _ _
    -- Comparison produces 0 or 1
    have hcmp_01 : cmp = 0 ∨ cmp = 1 :=
      gt512_01 x_hi x_lo r3hi r3lo hxhi_wm hxlo_wm hr3hi_lt hr3lo_lt
    -- Comparison iff: cmp ≠ 0 ↔ r³ > x
    have hcmp_iff : (cmp ≠ 0) ↔ (r * r * r > x_hi * WORD_MOD + x_lo) := by
      have hgt := gt512_correct x_hi x_lo r3hi r3lo hxhi_wm hxlo_wm hr3hi_lt hr3lo_lt
      simp only at hgt
      rw [hcube_eq] at hgt
      exact hgt
    -- r is icbrt x or icbrt x + 1
    have hrm : r = icbrt (x_hi * 2 ^ 256 + x_lo) ∨
               r = icbrt (x_hi * 2 ^ 256 + x_lo) + 1 := by omega
    rcases hrm with hr_eq | hr_eq
    · -- Case r = icbrt x: r³ ≤ x, so cmp = 0
      have h_cube_le := icbrt_cube_le (x_hi * 2 ^ 256 + x_lo)
      have h_not_gt : ¬(r * r * r > x_hi * WORD_MOD + x_lo) := by
        rw [hr_eq]; show ¬(_ > _); unfold WORD_MOD; omega
      have hcmp_zero : cmp = 0 := by
        rcases hcmp_01 with h | h
        · exact h
        · exfalso; exact h_not_gt (hcmp_iff.mp (by omega))
      rw [hcmp_zero, evmSub_eq_of_le _ 0 hr_lt (Nat.zero_le _)]
      exact hr_eq
    · -- Case r = icbrt x + 1: r³ > x, so cmp = 1
      have h_cube_gt := icbrt_lt_succ_cube (x_hi * 2 ^ 256 + x_lo)
      have h_gt : r * r * r > x_hi * WORD_MOD + x_lo := by
        rw [hr_eq]; show _ > _; unfold WORD_MOD; omega
      have hcmp_one : cmp = 1 := by
        rcases hcmp_01 with h | h
        · exfalso; have := hcmp_iff.mpr h_gt; omega
        · exact h
      rw [hcmp_one, evmSub_eq_of_le _ 1 hr_lt (by rw [hr_eq]; omega)]
      rw [hr_eq]; omega

end Cbrt512Spec

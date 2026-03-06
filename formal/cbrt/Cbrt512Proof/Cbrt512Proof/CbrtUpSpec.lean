/-
  Bridge proof: model_cbrtUp512_wrapper_evm computes cbrtUp512.

  The auto-generated model_cbrtUp512_wrapper_evm dispatches:
    x_hi = 0 ⟹ inlined 256-bit ceiling cbrt (= model_cbrt_up_evm from CbrtProof)
    x_hi > 0 ⟹ model_cbrt512_evm (within 1ulp) + cube-and-compare + increment
-/
import Cbrt512Proof.GeneratedCbrt512Model
import Cbrt512Proof.GeneratedCbrt512Spec
import Cbrt512Proof.Cbrt512Correct
import Cbrt512Proof.CbrtWrapperSpec
import CbrtProof.GeneratedCbrtModel
import CbrtProof.GeneratedCbrtSpec
import CbrtProof.CbrtCorrect

namespace Cbrt512Spec

open Cbrt512GeneratedModel

-- ============================================================================
-- Section 1: x_hi = 0 branch — bridge to model_cbrt_up_evm
-- ============================================================================

/-- When x_hi = 0, model_cbrtUp512_wrapper_evm equals model_cbrt_up_evm from CbrtProof. -/
theorem cbrtUp_wrapper_zero_eq_cbrt_up_evm (x_lo : Nat) :
    model_cbrtUp512_wrapper_evm 0 x_lo = CbrtGeneratedModel.model_cbrt_up_evm x_lo := by
  simp only [model_cbrtUp512_wrapper_evm, model_cbrt256_up_evm,
    CbrtGeneratedModel.model_cbrt_up_evm, CbrtGeneratedModel.model_cbrt_evm]
  simp only [evmEq_compat, evmShr_compat, evmAdd_compat, evmDiv_compat,
    evmSub_compat, evmClz_compat, evmShl_compat, evmLt_compat,
    evmMul_compat, u256_compat]
  simp only [cu256_zero, cu256_idem]
  simp (config := { decide := true })

-- ============================================================================
-- Section 2: Ceiling cbrt uniqueness
-- ============================================================================

/-- Ceiling cube root uniqueness: if x ≤ r³ and r is minimal, then r = cbrtUp512 x. -/
theorem cbrtUp512_unique (x r : Nat) (hx : x < 2 ^ 512)
    (hle : x ≤ r * r * r) (hmin : ∀ y, x ≤ y * y * y → r ≤ y) :
    r = cbrtUp512 x := by
  have ⟨hup_le, hup_min⟩ := cbrtUp512_correct x hx
  have h1 := hmin (cbrtUp512 x) hup_le
  have h2 := hup_min r hle
  omega

-- ============================================================================
-- Section 3: Main theorem — model_cbrtUp512_wrapper_evm = cbrtUp512
-- ============================================================================

set_option exponentiation.threshold 1024 in
/-- The EVM model of cbrtUp(uint512) computes cbrtUp512. -/
theorem model_cbrtUp512_wrapper_evm_correct (x_hi x_lo : Nat)
    (hxhi : x_hi < 2 ^ 256) (hxlo : x_lo < 2 ^ 256) :
    model_cbrtUp512_wrapper_evm x_hi x_lo = cbrtUp512 (x_hi * 2 ^ 256 + x_lo) := by
  by_cases hxhi0 : x_hi = 0
  · -- x_hi = 0: use 256-bit ceiling cbrt bridge
    subst hxhi0
    simp only [Nat.zero_mul, Nat.zero_add]
    rw [cbrtUp_wrapper_zero_eq_cbrt_up_evm]
    -- model_cbrt_up_evm x_lo satisfies ceiling cbrt spec
    have hspec := CbrtGeneratedModel.model_cbrt_up_evm_ceil_u256 x_lo hxlo
    -- Both satisfy the same uniqueness property
    have hx512 : x_lo < 2 ^ 512 := by
      calc x_lo < 2 ^ 256 := hxlo
        _ ≤ 2 ^ 512 := Nat.pow_le_pow_right (by omega) (by omega)
    exact cbrtUp512_unique x_lo (CbrtGeneratedModel.model_cbrt_up_evm x_lo) hx512
      hspec.1 hspec.2
  · -- x_hi > 0: model_cbrt512_evm within 1ulp + cube-and-compare + increment
    have hxhi_pos : 0 < x_hi := Nat.pos_of_ne_zero hxhi0
    have hxhi_wm : x_hi < WORD_MOD := by unfold WORD_MOD; exact hxhi
    have hxlo_wm : x_lo < WORD_MOD := by unfold WORD_MOD; exact hxlo
    -- Unfold wrapper and simplify u256
    unfold model_cbrtUp512_wrapper_evm
    simp only [u256_id' x_hi hxhi_wm, u256_id' x_lo hxlo_wm]
    -- Eliminate conditional: evmEq x_hi 0 = 0 since x_hi > 0
    have hneq : evmEq x_hi 0 = 0 := by
      rw [evmEq_eq' x_hi 0 hxhi_wm (by unfold WORD_MOD; omega)]
      exact if_neg (Nat.ne_of_gt hxhi_pos)
    have hcond_neg : ¬((evmEq x_hi 0) ≠ 0) := by rw [hneq]; omega
    rw [if_neg hcond_neg]
    -- Generalize the approximation
    generalize hr_def : model_cbrt512_evm x_hi x_lo = r
    -- Name cube sub-expressions via let (matching cube512_correct's structure)
    let r2lo := evmMul r r
    let mm1 := evmMulmod r r (evmNot 0)
    let r2hi := evmSub (evmSub mm1 r2lo) (evmLt mm1 r2lo)
    let mm2 := evmMulmod r2lo r (evmNot 0)
    let r3lo := evmMul r2lo r
    let r3hi := evmAdd (evmSub (evmSub mm2 r3lo) (evmLt mm2 r3lo)) (evmMul r2hi r)
    let cmp := evmOr (evmLt r3hi x_hi) (evmAnd (evmEq r3hi x_hi) (evmLt r3lo x_lo))
    -- Restate goal using named variables
    show evmAdd r cmp = cbrtUp512 (x_hi * 2 ^ 256 + x_lo)
    -- Get bounds from strengthened within_1ulp theorem
    have hbounds := model_cbrt512_evm_within_1ulp x_hi x_lo hxhi_pos
      (show x_hi < 2 ^ 256 from hxhi) (show x_lo < 2 ^ 256 from hxlo)
    simp only at hbounds
    rw [hr_def] at hbounds
    obtain ⟨h_lo, h_hi, hr_lt, hcube_lt, hr_succ_lt, h_overshoot⟩ := hbounds
    -- Cube decomposition: r3hi * WORD_MOD + r3lo = r³
    have hcube_eq : r3hi * WORD_MOD + r3lo = r * r * r := cube512_correct r hr_lt hcube_lt
    -- Bounds on r3hi and r3lo (EVM ops always < WORD_MOD)
    have hr3lo_lt : r3lo < WORD_MOD := by
      show evmMul (evmMul r r) r < WORD_MOD
      unfold evmMul u256 WORD_MOD; exact Nat.mod_lt _ (Nat.two_pow_pos 256)
    have hr3hi_lt : r3hi < WORD_MOD := by
      show evmAdd _ _ < WORD_MOD
      unfold evmAdd u256 WORD_MOD; exact Nat.mod_lt _ (Nat.two_pow_pos 256)
    -- Comparison produces 0 or 1
    have hcmp_01 : cmp = 0 ∨ cmp = 1 := by
      show evmOr (evmLt r3hi x_hi) (evmAnd (evmEq r3hi x_hi) (evmLt r3lo x_lo)) = 0 ∨ _ = 1
      exact evmOr_01 _ _ (evmLt_01 _ _ hr3hi_lt hxhi_wm)
        (evmAnd_01 _ _ (evmEq_01 _ _ hr3hi_lt hxhi_wm) (evmLt_01 _ _ hr3lo_lt hxlo_wm))
    -- Comparison iff: cmp ≠ 0 ↔ r³ < x
    have hcmp_iff : (cmp ≠ 0) ↔ (r * r * r < x_hi * WORD_MOD + x_lo) := by
      have hlt := lt512_correct x_hi x_lo r3hi r3lo hxhi_wm hxlo_wm hr3hi_lt hr3lo_lt
      simp only at hlt
      rw [hcube_eq] at hlt
      exact hlt
    -- x < 2^512 (needed for cbrtUp512_unique)
    have hx512 : x_hi * 2 ^ 256 + x_lo < 2 ^ 512 := by
      calc x_hi * 2 ^ 256 + x_lo
          ≤ (2 ^ 256 - 1) * 2 ^ 256 + (2 ^ 256 - 1) := by omega
        _ < 2 ^ 512 := by unfold WORD_MOD at hxhi_wm hxlo_wm; omega
    -- Case split on r³ vs x
    by_cases hlt_x : r * r * r < x_hi * WORD_MOD + x_lo
    · -- r³ < x: cmp = 1, result = r + 1
      -- r = icbrt x (r³ < x and r ≥ icbrt x imply r can't be icbrt x + 1)
      have hr_eq : r = icbrt (x_hi * 2 ^ 256 + x_lo) := by
        have hrm : r = icbrt (x_hi * 2 ^ 256 + x_lo) ∨
                   r = icbrt (x_hi * 2 ^ 256 + x_lo) + 1 := by omega
        rcases hrm with h | h
        · exact h
        · exfalso
          have := icbrt_lt_succ_cube (x_hi * 2 ^ 256 + x_lo)
          rw [h] at hlt_x; unfold WORD_MOD at hlt_x; omega
      have hcmp_one : cmp = 1 := by
        rcases hcmp_01 with h | h
        · exfalso; have := hcmp_iff.mpr hlt_x; omega
        · exact h
      rw [hcmp_one]
      have hr_add : evmAdd r 1 = r + 1 :=
        evmAdd_eq' r 1 hr_lt (by unfold WORD_MOD; omega) hr_succ_lt
      rw [hr_add, hr_eq]
      unfold cbrtUp512
      have h_icbrt_lt : icbrt (x_hi * 2 ^ 256 + x_lo) * icbrt (x_hi * 2 ^ 256 + x_lo) *
          icbrt (x_hi * 2 ^ 256 + x_lo) < x_hi * 2 ^ 256 + x_lo := by
        rw [hr_eq] at hlt_x; unfold WORD_MOD at hlt_x; exact hlt_x
      simp [h_icbrt_lt]
    · -- r³ ≥ x: cmp = 0, result = r
      -- hlt_x : ¬(r³ < x_hi * WORD_MOD + x_lo), i.e., r³ ≥ x
      have hge_x : x_hi * WORD_MOD + x_lo ≤ r * r * r := Nat.not_lt.mp hlt_x
      have hcmp_zero : cmp = 0 := by
        rcases hcmp_01 with h | h
        · exact h
        · exfalso; exact hlt_x (hcmp_iff.mp (by omega))
      rw [hcmp_zero]
      have hr_add : evmAdd r 0 = r :=
        evmAdd_eq' r 0 hr_lt (by unfold WORD_MOD; omega) (by omega)
      rw [hr_add]
      have hx_le_rcube : x_hi * 2 ^ 256 + x_lo ≤ r * r * r := by
        unfold WORD_MOD at hge_x; exact hge_x
      -- Case-split on r = icbrt x vs r = icbrt x + 1
      have hrm : r = icbrt (x_hi * 2 ^ 256 + x_lo) ∨
                 r = icbrt (x_hi * 2 ^ 256 + x_lo) + 1 := by omega
      rcases hrm with hr_eq | hr_eq
      · -- r = icbrt x and r³ ≥ x: perfect cube, cbrtUp = icbrt
        rw [hr_eq]
        unfold cbrtUp512
        have h_cube_le := icbrt_cube_le (x_hi * 2 ^ 256 + x_lo)
        -- icbrt(x)³ ≤ x and x ≤ r³ = icbrt(x)³, so icbrt(x)³ = x
        have hx_le_icbrt : x_hi * 2 ^ 256 + x_lo ≤
            icbrt (x_hi * 2 ^ 256 + x_lo) * icbrt (x_hi * 2 ^ 256 + x_lo) *
            icbrt (x_hi * 2 ^ 256 + x_lo) := by
          rw [← hr_eq]; exact hx_le_rcube
        have h_eq : ¬(icbrt (x_hi * 2 ^ 256 + x_lo) * icbrt (x_hi * 2 ^ 256 + x_lo) *
            icbrt (x_hi * 2 ^ 256 + x_lo) < x_hi * 2 ^ 256 + x_lo) :=
          Nat.not_lt.mpr hx_le_icbrt
        simp [h_eq]
      · -- r = icbrt x + 1: x is not a perfect cube (from h_overshoot)
        have h_rcube_gt : r * r * r > x_hi * 2 ^ 256 + x_lo := by
          have := icbrt_lt_succ_cube (x_hi * 2 ^ 256 + x_lo)
          rw [hr_eq]; omega
        have h_not_perfect : icbrt (x_hi * 2 ^ 256 + x_lo) *
            icbrt (x_hi * 2 ^ 256 + x_lo) *
            icbrt (x_hi * 2 ^ 256 + x_lo) < x_hi * 2 ^ 256 + x_lo :=
          h_overshoot h_rcube_gt
        rw [hr_eq]
        exact cbrtUp512_unique (x_hi * 2 ^ 256 + x_lo)
          (icbrt (x_hi * 2 ^ 256 + x_lo) + 1)
          hx512
          (by rw [← hr_eq]; exact hx_le_rcube)
          (fun y hy => by
            -- Need: icbrt(x) + 1 ≤ y given x ≤ y³ and icbrt(x)³ < x
            have : ¬(y ≤ icbrt (x_hi * 2 ^ 256 + x_lo)) := by
              intro hle
              exact Nat.lt_irrefl (x_hi * 2 ^ 256 + x_lo)
                (Nat.lt_of_le_of_lt (Nat.le_trans hy (cube_monotone hle)) h_not_perfect)
            omega)

end Cbrt512Spec

/-
  Composition: the full 512-bit cbrt algorithm gives icbrt(x_norm) ± 1.

  Combines sub-lemmas A (upper), B (lower), E1 (range), E2 (overshoot),
  the QC bridge, and the undershoot analysis into:
    icbrt(x_norm) ≤ r_qc ≤ icbrt(x_norm) + 1

  Also contains the P1 (undershoot fires → r_qc ≤ icbrt) and
  P2 c>1 (check = 0 → icbrt ≤ r_qc) proofs.
-/
import Cbrt512Proof.GeneratedCbrt512Model
import Cbrt512Proof.CbrtBaseCase
import Cbrt512Proof.CbrtKaratsubaQuotient
import Cbrt512Proof.CbrtAlgebraic
import Cbrt512Proof.EvmBridge
import Cbrt512Proof.CbrtQCBridge
import Cbrt512Proof.CbrtSublemmaA
import Cbrt512Proof.CbrtSublemmaB
import Cbrt512Proof.CbrtRangeBounds
import Cbrt512Proof.CbrtOvershoot
import CbrtProof.CbrtCorrect

namespace Cbrt512Spec

open Cbrt512GeneratedModel

-- ============================================================================
-- Combined: r_qc_properties from sub-lemmas A, B, E
-- ============================================================================

/-- The quadratic-corrected result satisfies within-1-ulp, cube bound, and
    overshoot properties. Composed from sub-lemmas A, B, E1 (r_qc ≤ R_MAX),
    and E2 (overshoot → not perfect cube). -/
theorem r_qc_properties (x_hi_1 x_lo_1 : Nat)
    (hxhi_lo : 2 ^ 253 ≤ x_hi_1) (hxhi_hi : x_hi_1 < WORD_MOD)
    (hxlo : x_lo_1 < WORD_MOD) :
    let w := x_hi_1 / 4
    let m := icbrt w
    let res := w - m * m * m
    let d := 3 * (m * m)
    let limb_hi := (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172
    let r_lo := (res * 2 ^ 86 + limb_hi) / d
    let R := m * 2 ^ 86
    let correction := r_lo * r_lo / R
    let r_qc := R + r_lo - correction
    let x_norm := x_hi_1 * 2 ^ 256 + x_lo_1
    icbrt x_norm ≤ r_qc + 1 ∧ r_qc ≤ icbrt x_norm + 1 ∧
    r_qc * r_qc * r_qc < WORD_MOD * WORD_MOD ∧
    (r_qc * r_qc * r_qc > x_norm →
      icbrt x_norm * icbrt x_norm * icbrt x_norm < x_norm) := by
  simp only
  -- Sub-lemmas (simp only inlines the let-bindings, matching the goal)
  have hA := r_qc_succ2_cube_gt x_hi_1 x_lo_1 hxhi_lo hxhi_hi hxlo
  have hB := r_qc_pred_cube_le x_hi_1 x_lo_1 hxhi_lo hxhi_hi hxlo
  have hE1 := r_qc_le_r_max x_hi_1 x_lo_1 hxhi_lo hxhi_hi hxlo
  have hE2 := r_qc_no_overshoot_on_cubes x_hi_1 x_lo_1 hxhi_lo hxhi_hi hxlo
  simp only at hA hB hE1 hE2
  have hcube_le := icbrt_cube_le (x_hi_1 * 2 ^ 256 + x_lo_1)
  have hsucc_gt := icbrt_lt_succ_cube (x_hi_1 * 2 ^ 256 + x_lo_1)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- [1] icbrt(x_norm) ≤ r_qc + 1: if r_qc + 1 < icbrt then (r_qc+2)³ ≤ icbrt³ ≤ x_norm,
    --     contradicting hA: x_norm < (r_qc+2)³.
    exact Nat.not_lt.mp fun h =>
      absurd hA (Nat.not_lt.mpr (Nat.le_trans (cube_monotone h) hcube_le))
  · -- [2] r_qc ≤ icbrt(x_norm) + 1: if icbrt+1 < r_qc then (icbrt+1)³ ≤ (r_qc-1)³ ≤ x_norm,
    --     contradicting hsucc_gt: x_norm < (icbrt+1)³.
    exact Nat.not_lt.mp fun h =>
      absurd hsucc_gt
        (Nat.not_lt.mpr (Nat.le_trans (cube_monotone (Nat.le_sub_one_of_lt h)) hB))
  · -- [3] r_qc³ < WORD_MOD²: r_qc ≤ R_MAX (E1), so r_qc³ ≤ R_MAX³ < WORD_MOD² (native_decide).
    exact Nat.lt_of_le_of_lt (cube_monotone hE1) r_max_cube_lt_wm2
  · -- [4] r_qc³ > x_norm → icbrt³ < x_norm: from E2.
    exact hE2

-- ============================================================================
-- Range bounds helper
-- ============================================================================

/-- r_qc < 2^172 (and hence < WORD_MOD). -/
theorem r_qc_lt_pow172 (x_hi_1 x_lo_1 : Nat)
    (hxhi_lo : 2 ^ 253 ≤ x_hi_1) (hxhi_hi : x_hi_1 < WORD_MOD)
    (hxlo : x_lo_1 < WORD_MOD) :
    let w := x_hi_1 / 4
    let m := icbrt w
    let res := w - m * m * m
    let d := 3 * (m * m)
    let limb_hi := (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172
    let r_lo := (res * 2 ^ 86 + limb_hi) / d
    let R := m * 2 ^ 86
    let correction := r_lo * r_lo / R
    let r_qc := R + r_lo - correction
    r_qc < 2 ^ 172 := by
  simp only
  -- Get base case properties
  have hbc := model_cbrtBaseCase_evm_correct x_hi_1 hxhi_lo hxhi_hi
  have hm_lo : 2 ^ 83 ≤ icbrt (x_hi_1 / 4) := hbc.2.2.2.1
  have hm_hi : icbrt (x_hi_1 / 4) < 2 ^ 85 := hbc.2.2.2.2.1
  have hres_bound : x_hi_1 / 4 - icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)
      ≤ 3 * (icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)) + 3 * icbrt (x_hi_1 / 4) :=
    hbc.2.2.2.2.2.2.1
  have hd_pos : 3 * (icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)) > 0 := hbc.2.2.2.2.2.2.2.2.2.2
  -- Abbreviate
  let m := icbrt (x_hi_1 / 4)
  let res := x_hi_1 / 4 - m * m * m
  let d := 3 * (m * m)
  let limb_hi := (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172
  let r_lo := (res * 2 ^ 86 + limb_hi) / d
  -- R < 2^171
  have hR_lt : m * 2 ^ 86 < 2 ^ 171 :=
    calc m * 2 ^ 86
        < 2 ^ 85 * 2 ^ 86 := Nat.mul_lt_mul_of_pos_right hm_hi (Nat.two_pow_pos 86)
      _ = 2 ^ 171 := by rw [← Nat.pow_add]
  -- limb_hi < 2^86
  have hlimb_bound : limb_hi < 2 ^ 86 := by
    show (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172 < 2 ^ 86
    have hmod4 : x_hi_1 % 4 < 4 := Nat.mod_lt _ (by omega)
    have hdiv : x_lo_1 / 2 ^ 172 < 2 ^ 84 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 172)]
      calc x_lo_1 < WORD_MOD := hxlo
        _ = 2 ^ 84 * 2 ^ 172 := by unfold WORD_MOD; rw [← Nat.pow_add]
    have hprod : (x_hi_1 % 4) * 2 ^ 84 < 2 ^ 86 :=
      calc (x_hi_1 % 4) * 2 ^ 84 < 4 * 2 ^ 84 :=
              Nat.mul_lt_mul_of_pos_right hmod4 (Nat.two_pow_pos 84)
        _ = 2 ^ 86 := by rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add]
    omega
  -- r_lo < 2^87
  have hr_lo_bound : r_lo < 2 ^ 87 := by
    show (res * 2 ^ 86 + limb_hi) / d < 2 ^ 87
    rw [Nat.div_lt_iff_lt_mul hd_pos]
    -- 3m² + 3m + 1 ≤ 2*(3m²) = 6m²  needs  3m + 1 ≤ 3m²  needs  m + 1/3 ≤ m²
    -- From m ≥ 2: m² ≥ 2m ≥ m + m ≥ m + 2 > m + 1/3
    have h2m : 2 * m ≤ m * m := Nat.mul_le_mul_right m (by omega)
    have h6m2 : 3 * (m * m) + 3 * m + 1 ≤ 2 * (3 * (m * m)) := by omega
    calc res * 2 ^ 86 + limb_hi
        < (res + 1) * 2 ^ 86 := by omega
      _ ≤ (3 * (m * m) + 3 * m + 1) * 2 ^ 86 := by
          apply Nat.mul_le_mul_right
          show res + 1 ≤ 3 * (m * m) + 3 * m + 1
          exact Nat.succ_le_succ hres_bound
      _ ≤ (2 * (3 * (m * m))) * 2 ^ 86 := Nat.mul_le_mul_right _ h6m2
      _ = 2 ^ 87 * (3 * (m * m)) := by
          -- 2 * (3*(m*m)) * 2^86 = (2*2^86) * (3*(m*m)) = 2^87 * d
          have h287 : (2 : Nat) ^ 87 = 2 * 2 ^ 86 := by
            rw [show (87 : Nat) = 1 + 86 from rfl, Nat.pow_add]
          omega
  -- r_qc ≤ R + r_lo < 2^171 + 2^87 < 2^172
  show m * 2 ^ 86 + r_lo - r_lo * r_lo / (m * 2 ^ 86) < 2 ^ 172
  have hsub : m * 2 ^ 86 + r_lo - r_lo * r_lo / (m * 2 ^ 86) ≤ m * 2 ^ 86 + r_lo :=
    Nat.sub_le _ _
  have h2172 : (2 : Nat) ^ 172 = 2 * 2 ^ 171 := by
    rw [show (172 : Nat) = 1 + 171 from rfl, Nat.pow_add]
  omega

-- ============================================================================
-- Undershoot check helper lemmas
-- ============================================================================

/-- If a ||| (b &&& c) = 1 with all values ≤ 1, then a = 1 ∨ (b = 1 ∧ c = 1). -/
theorem or_and_eq_one_cases (a b c : Nat) (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1)
    (h : a ||| (b &&& c) = 1) : a = 1 ∨ (b = 1 ∧ c = 1) := by
  have : a = 0 ∨ a = 1 := by omega
  have : b = 0 ∨ b = 1 := by omega
  have : c = 0 ∨ c = 1 := by omega
  rcases ‹a = 0 ∨ a = 1› with rfl | rfl
  · rcases ‹b = 0 ∨ b = 1› with rfl | rfl <;>
    rcases ‹c = 0 ∨ c = 1› with rfl | rfl <;> simp_all
  · left; rfl

-- ============================================================================
-- Undershoot algebraic sub-lemmas
-- ============================================================================

/-- If eps3 < rem and R ≤ 2^172, then eps3 * R ≤ rem * 2^172. -/
theorem eps3_lt_rem_implies_prod_le (eps3 rem R : Nat)
    (hR_le : R ≤ 2 ^ 172)
    (h_lt : eps3 < rem) :
    eps3 * R ≤ rem * 2 ^ 172 :=
  Nat.le_trans
    (Nat.mul_le_mul_right _ (Nat.le_of_lt h_lt))
    (Nat.mul_le_mul_left _ hR_le)

/-- Exact split-limb comparison implies the product inequality.
    When a/2^86 = b/2^86 and (a%2^86)*m < (b%2^86)*2^86 and m ≤ 2^86,
    then a*(m*2^86) ≤ b*2^172.
    Proof: decompose a = 2^86*h + a_lo, b = 2^86*h + b_lo (same h).
    First terms bounded by m ≤ 2^86, second terms by the comparison. -/
theorem split_limb_implies_prod_le (a b m : Nat)
    (hm_le : m ≤ 2 ^ 86)
    (h_eq : a / 2 ^ 86 = b / 2 ^ 86)
    (h_lo : (a % 2 ^ 86) * m < (b % 2 ^ 86) * 2 ^ 86) :
    a * (m * 2 ^ 86) ≤ b * 2 ^ 172 := by
  have hda := Nat.div_add_mod a (2 ^ 86)  -- 2^86 * (a/2^86) + a%2^86 = a
  have hdb := Nat.div_add_mod b (2 ^ 86)  -- 2^86 * (b/2^86) + b%2^86 = b
  have h2172 : (2 : Nat) ^ 172 = 2 ^ 86 * 2 ^ 86 := by
    rw [show (172 : Nat) = 86 + 86 from rfl, Nat.pow_add]
  rw [← hda, ← hdb, h_eq, h2172]
  rw [Nat.add_mul, Nat.add_mul]
  apply Nat.add_le_add
  · -- 2^86*h*(m*2^86) ≤ 2^86*h*(2^86*2^86) since m ≤ 2^86
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hm_le)
  · -- a%2^86*(m*2^86) ≤ b%2^86*(2^86*2^86)
    apply Nat.le_of_lt
    rw [show a % 2 ^ 86 * (m * 2 ^ 86) = (a % 2 ^ 86 * m) * 2 ^ 86 from by
          simp [Nat.mul_assoc, Nat.mul_comm m, Nat.mul_left_comm]]
    rw [show b % 2 ^ 86 * (2 ^ 86 * 2 ^ 86) = (b % 2 ^ 86 * 2 ^ 86) * 2 ^ 86 from by
          simp [Nat.mul_assoc]]
    exact Nat.mul_lt_mul_of_pos_right h_lo (Nat.two_pow_pos 86)

-- ============================================================================
-- Undershoot check algebraic consequence
-- ============================================================================

/-- When the QC model returns r_qc + 1 (undershoot correction), the split-limb
    comparison implies nat_rem * 2^172 > 3 * R * ε where R = m * 2^86 and
    ε = r_lo² mod R.  This is the key inequality making the x_norm decomposition
    positive: x_norm - r_qc³ = 3Rc(2r_lo-c) + (rem*2^172 - 3Rε) + c_tail - t³,
    and with this inequality, the (rem*2^172 - 3Rε) term is non-negative. -/
theorem undershoot_implies_rem_gt_3Reps
    (m nat_r_lo nat_rem : Nat)
    (hm_wm : m < WORD_MOD) (hr_lo_wm : nat_r_lo < WORD_MOD) (hrem_wm : nat_rem < WORD_MOD)
    (hm_pos : 2 ≤ m) (hm_hi : m < 2 ^ 85)
    (hr_lo_bound : nat_r_lo < 2 ^ 87)
    (hc_gt1 : nat_r_lo * nat_r_lo / (m * 2 ^ 86) > 1)
    (hr1_eq : model_cbrtQuadraticCorrection_evm m nat_r_lo nat_rem =
        m * 2 ^ 86 + nat_r_lo - nat_r_lo * nat_r_lo / (m * 2 ^ 86) + 1) :
    nat_r_lo * nat_r_lo % (m * 2 ^ 86) * 3 * (m * 2 ^ 86) ≤
        nat_rem * 2 ^ 172 := by
  -- ======== Bounds setup (same as QC bridge proof) ========
  have hR_ge : 2 ^ 87 ≤ m * 2 ^ 86 :=
    calc 2 ^ 87 = 2 * 2 ^ 86 := by
          rw [show (87 : Nat) = 1 + 86 from rfl, Nat.pow_add]
      _ ≤ m * 2 ^ 86 := Nat.mul_le_mul_right _ hm_pos
  have hR_lt : m * 2 ^ 86 < 2 ^ 171 :=
    calc m * 2 ^ 86
        < 2 ^ 85 * 2 ^ 86 := Nat.mul_lt_mul_of_pos_right hm_hi (Nat.two_pow_pos 86)
      _ = 2 ^ 171 := by rw [← Nat.pow_add]
  have hR_wm : m * 2 ^ 86 < WORD_MOD := by unfold WORD_MOD; omega
  have hR_pos : 0 < m * 2 ^ 86 := by omega
  have hr_lo_sq : nat_r_lo * nat_r_lo < 2 ^ 174 := by
    cases Nat.eq_or_lt_of_le (Nat.zero_le nat_r_lo) with
    | inl h => rw [← h]; simp
    | inr h =>
      calc nat_r_lo * nat_r_lo
          < nat_r_lo * 2 ^ 87 := Nat.mul_lt_mul_of_pos_left hr_lo_bound h
        _ ≤ 2 ^ 87 * 2 ^ 87 := Nat.mul_le_mul_right _ (Nat.le_of_lt hr_lo_bound)
        _ = 2 ^ 174 := by rw [← Nat.pow_add]
  have hr_lo_sq_wm : nat_r_lo * nat_r_lo < WORD_MOD := by unfold WORD_MOD; omega
  have hR_gt_rlo : nat_r_lo < m * 2 ^ 86 := by omega
  have hc_le : nat_r_lo * nat_r_lo / (m * 2 ^ 86) ≤ nat_r_lo := by
    cases Nat.eq_or_lt_of_le (Nat.zero_le nat_r_lo) with
    | inl h => rw [← h]; simp
    | inr h =>
      exact Nat.le_of_lt ((Nat.div_lt_iff_lt_mul hR_pos).mpr
        (Nat.mul_lt_mul_of_pos_left hR_gt_rlo h))
  have hcR_le : (nat_r_lo * nat_r_lo / (m * 2 ^ 86)) * (m * 2 ^ 86) ≤ nat_r_lo * nat_r_lo :=
    Nat.div_mul_le_self _ _
  let c := nat_r_lo * nat_r_lo / (m * 2 ^ 86)
  have hc_wm : c < WORD_MOD := Nat.lt_of_le_of_lt hc_le hr_lo_wm
  have hcR_wm : c * (m * 2 ^ 86) < WORD_MOD :=
    Nat.lt_of_le_of_lt hcR_le hr_lo_sq_wm
  -- ======== EVM-to-Nat reduction lemmas ========
  have hR_eq : evmShl (evmAnd (evmAnd 86 255) 255) m = m * 2 ^ 86 := by
    rw [qc_const_86, evmShl_eq' 86 m (by omega) hm_wm]
    exact Nat.mod_eq_of_lt hR_wm
  have hSq_eq : evmMul nat_r_lo nat_r_lo = nat_r_lo * nat_r_lo := by
    rw [evmMul_eq' nat_r_lo nat_r_lo hr_lo_wm hr_lo_wm]; exact Nat.mod_eq_of_lt hr_lo_sq_wm
  have hC_eq : evmDiv (nat_r_lo * nat_r_lo) (m * 2 ^ 86) = c :=
    evmDiv_eq' _ _ hr_lo_sq_wm hR_pos hR_wm
  have hCR_eq : evmMul c (m * 2 ^ 86) = c * (m * 2 ^ 86) := by
    rw [evmMul_eq' c _ hc_wm hR_wm]; exact Nat.mod_eq_of_lt hcR_wm
  have hResid_eq : evmSub (nat_r_lo * nat_r_lo) (c * (m * 2 ^ 86)) =
      nat_r_lo * nat_r_lo % (m * 2 ^ 86) := by
    rw [evmSub_eq_of_le _ _ hr_lo_sq_wm hcR_le,
        show c * (m * 2 ^ 86) = (m * 2 ^ 86) * c from Nat.mul_comm _ _]
    have hdm := Nat.div_add_mod (nat_r_lo * nat_r_lo) (m * 2 ^ 86)
    rw [Nat.add_comm] at hdm
    exact Nat.sub_eq_of_eq_add hdm.symm
  have hmod_lt : nat_r_lo * nat_r_lo % (m * 2 ^ 86) < WORD_MOD :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ hR_pos) (by unfold WORD_MOD; omega)
  have heps3_wm : (nat_r_lo * nat_r_lo % (m * 2 ^ 86)) * 3 < WORD_MOD := by
    calc (nat_r_lo * nat_r_lo % (m * 2 ^ 86)) * 3
        < (m * 2 ^ 86) * 3 := Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ hR_pos) (by omega)
      _ < 2 ^ 171 * 3 := Nat.mul_lt_mul_of_pos_right hR_lt (by omega)
      _ < WORD_MOD := by unfold WORD_MOD; omega
  have hEps3_eq : evmMul (nat_r_lo * nat_r_lo % (m * 2 ^ 86)) 3 =
      (nat_r_lo * nat_r_lo % (m * 2 ^ 86)) * 3 := by
    rw [evmMul_eq' _ 3 hmod_lt (by unfold WORD_MOD; omega)]
    exact Nat.mod_eq_of_lt heps3_wm
  have hSub_eq : evmSub nat_r_lo c = nat_r_lo - c :=
    evmSub_eq_of_le _ _ hr_lo_wm hc_le
  have hGt_eq : evmGt c 1 = if c > 1 then 1 else 0 :=
    evmGt_eq' c 1 hc_wm (by unfold WORD_MOD; omega)
  -- ======== Abbreviations for eps3 ========
  let eps3 := (nat_r_lo * nat_r_lo % (m * 2 ^ 86)) * 3
  -- eps3 < WORD_MOD (carry through for omega)
  have heps3_wm' : eps3 < WORD_MOD := heps3_wm
  -- ======== Unfold model in hr1_eq and simplify ========
  unfold model_cbrtQuadraticCorrection_evm at hr1_eq
  simp only [u256_id' m hm_wm, u256_id' nat_r_lo hr_lo_wm, u256_id' nat_rem hrem_wm,
             hR_eq, hSq_eq, hC_eq, hCR_eq, hResid_eq, hEps3_eq, hSub_eq, hGt_eq] at hr1_eq
  -- Now hr1_eq is about the if-then-else on c > 1
  rw [if_pos hc_gt1] at hr1_eq
  -- The if branch: evmAdd (nat_r_lo - c) (check) where check is the undershoot OR expression
  -- Since c > 1, the inner if is also taken
  rw [if_pos (show (1 : Nat) ≠ 0 from by omega)] at hr1_eq
  -- ======== Reduce the check sub-expressions ========
  -- eps3 / 2^86 and rem / 2^86 (the high parts)
  have hShr_eps3 : evmShr (evmAnd (evmAnd 86 255) 255) eps3 = eps3 / 2 ^ 86 := by
    rw [qc_const_86, evmShr_eq' 86 eps3 (by omega) heps3_wm']
  have hShr_rem : evmShr (evmAnd (evmAnd 86 255) 255) nat_rem = nat_rem / 2 ^ 86 := by
    rw [qc_const_86, evmShr_eq' 86 nat_rem (by omega) hrem_wm]
  have heps3_hi_wm : eps3 / 2 ^ 86 < WORD_MOD :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) heps3_wm'
  have hrem_hi_wm : nat_rem / 2 ^ 86 < WORD_MOD := by
    unfold WORD_MOD; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hrem_wm
  -- evmLt on high parts
  have hLt_hi : evmLt (eps3 / 2 ^ 86) (nat_rem / 2 ^ 86) =
      if eps3 / 2 ^ 86 < nat_rem / 2 ^ 86 then 1 else 0 :=
    evmLt_eq' _ _ heps3_hi_wm hrem_hi_wm
  -- evmEq on high parts
  have hEq_hi : evmEq (eps3 / 2 ^ 86) (nat_rem / 2 ^ 86) =
      if eps3 / 2 ^ 86 = nat_rem / 2 ^ 86 then 1 else 0 :=
    evmEq_eq' _ _ heps3_hi_wm hrem_hi_wm
  -- Low parts: evmAnd with mask86 = mod 2^86
  have hAnd_eps3 : evmAnd eps3 77371252455336267181195263 = eps3 % 2 ^ 86 :=
    evmAnd_mask86_eq_mod eps3 heps3_wm'
  have hAnd_rem : evmAnd nat_rem 77371252455336267181195263 = nat_rem % 2 ^ 86 :=
    evmAnd_mask86_eq_mod nat_rem hrem_wm
  -- Low part products
  have heps3_lo_wm : eps3 % 2 ^ 86 < WORD_MOD := by
    unfold WORD_MOD; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos 86)) (by omega)
  have hrem_lo_wm : nat_rem % 2 ^ 86 < WORD_MOD := by
    unfold WORD_MOD; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos 86)) (by omega)
  have hMul_lo : evmMul (eps3 % 2 ^ 86) m = ((eps3 % 2 ^ 86) * m) % WORD_MOD :=
    evmMul_eq' _ _ heps3_lo_wm hm_wm
  -- (eps3 % 2^86) * m < 2^86 * 2^85 = 2^171 < WORD_MOD
  have hprod_eps3_bound : (eps3 % 2 ^ 86) * m < 2 ^ 171 :=
    calc (eps3 % 2 ^ 86) * m
        < 2 ^ 86 * m := Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (Nat.two_pow_pos 86)) (by omega)
      _ < 2 ^ 86 * 2 ^ 85 := Nat.mul_lt_mul_of_pos_left hm_hi (Nat.two_pow_pos 86)
      _ = 2 ^ 171 := by rw [← Nat.pow_add]
  have hprod_eps3_wm : (eps3 % 2 ^ 86) * m < WORD_MOD := by unfold WORD_MOD; omega
  rw [Nat.mod_eq_of_lt hprod_eps3_wm] at hMul_lo
  -- evmShl 86 (rem % 2^86) = (rem % 2^86) * 2^86
  have hShl_rem : evmShl (evmAnd (evmAnd 86 255) 255) (nat_rem % 2 ^ 86) =
      (nat_rem % 2 ^ 86) * 2 ^ 86 := by
    rw [qc_const_86, evmShl_eq' 86 (nat_rem % 2 ^ 86) (by omega) hrem_lo_wm]
    -- (rem % 2^86) * 2^86 < 2^86 * 2^86 = 2^172 < WORD_MOD
    have : (nat_rem % 2 ^ 86) * 2 ^ 86 < 2 ^ 172 :=
      calc (nat_rem % 2 ^ 86) * 2 ^ 86
          < 2 ^ 86 * 2 ^ 86 := Nat.mul_lt_mul_of_pos_right
            (Nat.mod_lt _ (Nat.two_pow_pos 86)) (Nat.two_pow_pos 86)
        _ = 2 ^ 172 := by rw [← Nat.pow_add]
    exact Nat.mod_eq_of_lt (by unfold WORD_MOD; omega)
  -- evmLt on low products
  have hprod_rem_bound : (nat_rem % 2 ^ 86) * 2 ^ 86 < WORD_MOD := by
    calc (nat_rem % 2 ^ 86) * 2 ^ 86
        < 2 ^ 86 * 2 ^ 86 := Nat.mul_lt_mul_of_pos_right
          (Nat.mod_lt _ (Nat.two_pow_pos 86)) (Nat.two_pow_pos 86)
      _ = 2 ^ 172 := by rw [← Nat.pow_add]
    unfold WORD_MOD; omega
  have hLt_lo : evmLt ((eps3 % 2 ^ 86) * m) ((nat_rem % 2 ^ 86) * 2 ^ 86) =
      if (eps3 % 2 ^ 86) * m < (nat_rem % 2 ^ 86) * 2 ^ 86 then 1 else 0 :=
    evmLt_eq' _ _ hprod_eps3_wm hprod_rem_bound
  -- ======== Simplify the check in hr1_eq using rw ========
  rw [hShr_eps3, hShr_rem, hLt_hi, hAnd_eps3, hAnd_rem, hMul_lo, hShl_rem, hLt_lo,
      hEq_hi] at hr1_eq
  -- Reduce evmAnd/evmOr on boolean results to &&&/|||
  rw [evmAnd_eq'
      (if eps3 / 2 ^ 86 = nat_rem / 2 ^ 86 then 1 else 0)
      (if (eps3 % 2 ^ 86) * m < (nat_rem % 2 ^ 86) * 2 ^ 86 then 1 else 0)
      (by split <;> unfold WORD_MOD <;> omega)
      (by split <;> unfold WORD_MOD <;> omega)] at hr1_eq
  rw [evmOr_eq'
      (if eps3 / 2 ^ 86 < nat_rem / 2 ^ 86 then 1 else 0)
      ((if eps3 / 2 ^ 86 = nat_rem / 2 ^ 86 then 1 else 0) &&&
       (if (eps3 % 2 ^ 86) * m < (nat_rem % 2 ^ 86) * 2 ^ 86 then 1 else 0))
      (by split <;> unfold WORD_MOD <;> omega)
      (by have := and_le_one _ _
            (by split <;> omega : (if eps3 / 2 ^ 86 = nat_rem / 2 ^ 86 then 1 else 0) ≤ 1)
            (by split <;> omega : (if (eps3 % 2 ^ 86) * m < (nat_rem % 2 ^ 86) * 2 ^ 86 then 1 else 0) ≤ 1)
          unfold WORD_MOD; omega)] at hr1_eq
  -- ======== evmAdd simplifications ========
  -- Abbreviate the check value
  generalize hcheck : (if eps3 / 2 ^ 86 < nat_rem / 2 ^ 86 then 1 else 0) |||
      ((if eps3 / 2 ^ 86 = nat_rem / 2 ^ 86 then 1 else 0) &&&
       (if (eps3 % 2 ^ 86) * m < (nat_rem % 2 ^ 86) * 2 ^ 86 then 1 else 0)) = check at hr1_eq
  have hcheck_le : check ≤ 1 := by
    rw [← hcheck]
    exact or_le_one _ _
      (by split <;> omega)
      (and_le_one _ _
        (by split <;> omega) (by split <;> omega))
  -- Simplify the two evmAdd calls
  have h_rloc_wm : nat_r_lo - c < WORD_MOD := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hr_lo_wm
  have h_check_wm : check < WORD_MOD := by unfold WORD_MOD; omega
  have h_inner : nat_r_lo - c + check < WORD_MOD := by unfold WORD_MOD; omega
  rw [evmAdd_eq' _ _ h_rloc_wm h_check_wm h_inner,
      evmAdd_eq' _ _ hR_wm h_inner (by unfold WORD_MOD; omega)] at hr1_eq
  -- Now hr1_eq : m * 2^86 + (nat_r_lo - c + check) = m * 2^86 + nat_r_lo - c + 1
  -- Extract check = 1
  have hcheck_eq_1 : check = 1 := by omega
  -- ======== Case split using or_and_eq_one_cases ========
  rw [← hcheck] at hcheck_eq_1
  have h_cases := or_and_eq_one_cases _ _ _
    (by split <;> omega) (by split <;> omega) (by split <;> omega)
    hcheck_eq_1
  rcases h_cases with h_hi_lt | ⟨h_hi_eq, h_lo_lt⟩
  · -- Case 1: eps3 / 2^86 < nat_rem / 2^86
    have : eps3 / 2 ^ 86 < nat_rem / 2 ^ 86 := by
      by_cases h : eps3 / 2 ^ 86 < nat_rem / 2 ^ 86
      · exact h
      · simp [h] at h_hi_lt
    have hlt := div_lt_implies_lt eps3 nat_rem this
    -- eps3 * R ≤ rem * 2^172 from eps3 < rem and R ≤ 2^172
    exact eps3_lt_rem_implies_prod_le eps3 nat_rem (m * 2 ^ 86)
      (by omega : m * 2 ^ 86 ≤ 2 ^ 172) hlt
  · -- Case 2: eps3 / 2^86 = nat_rem / 2^86 ∧ (eps3 % 2^86) * m < (nat_rem % 2^86) * 2^86
    have h_eq86 : eps3 / 2 ^ 86 = nat_rem / 2 ^ 86 := by
      by_cases h : eps3 / 2 ^ 86 = nat_rem / 2 ^ 86
      · exact h
      · simp [h] at h_hi_eq
    have h_lo86 : (eps3 % 2 ^ 86) * m < (nat_rem % 2 ^ 86) * 2 ^ 86 := by
      by_cases h : (eps3 % 2 ^ 86) * m < (nat_rem % 2 ^ 86) * 2 ^ 86
      · exact h
      · simp [h] at h_lo_lt
    -- eps3 * (m * 2^86) ≤ rem * 2^172 from the split-limb comparison
    exact split_limb_implies_prod_le eps3 nat_rem m
      (by omega : m ≤ 2 ^ 86) h_eq86 h_lo86

-- ============================================================================
-- r_qc³ < x_norm: the algebraic core
-- ============================================================================

/-- When the undershoot check fires (hr1_eq), r_qc³ < x_norm.
    Proof: decompose x_norm = R³ + 3R²·r_lo + rem·2^172 + c_tail,
    expand r_qc³ = (R+t)³ = R³ + 3R²t + 3Rt² + t³ where t = r_lo - c.
    x_norm - r_qc³ = 3R²c + rem·2^172 + c_tail - 3Rt² - t³.
    From undershoot: rem·2^172 ≥ 3Rε ⟹ 3R²c + rem·2^172 ≥ 3R·r_lo².
    From sq_sum_expand: 3R·r_lo² = 3Rt² + 6Rtc + 3Rc², so t³ < 6Rtc + 3Rc². -/
theorem r_qc_cube_lt_x_norm (x_hi_1 x_lo_1 : Nat)
    (hxhi_lo : 2 ^ 253 ≤ x_hi_1) (hxhi_hi : x_hi_1 < WORD_MOD)
    (hxlo : x_lo_1 < WORD_MOD)
    (m : Nat) (hm_eq : m = icbrt (x_hi_1 / 4))
    (nat_r_lo nat_rem : Nat)
    (hr_lo_eq : nat_r_lo = ((x_hi_1 / 4 - m * m * m) * 2 ^ 86 +
        (x_hi_1 % 4 * 2 ^ 84 + x_lo_1 / 2 ^ 172)) / (3 * (m * m)))
    (hrem_eq : nat_rem = ((x_hi_1 / 4 - m * m * m) * 2 ^ 86 +
        (x_hi_1 % 4 * 2 ^ 84 + x_lo_1 / 2 ^ 172)) % (3 * (m * m)))
    (hr1_eq : model_cbrtQuadraticCorrection_evm m nat_r_lo nat_rem =
        m * 2 ^ 86 + nat_r_lo - nat_r_lo * nat_r_lo / (m * 2 ^ 86) + 1) :
    (m * 2 ^ 86 + nat_r_lo - nat_r_lo * nat_r_lo / (m * 2 ^ 86)) *
    (m * 2 ^ 86 + nat_r_lo - nat_r_lo * nat_r_lo / (m * 2 ^ 86)) *
    (m * 2 ^ 86 + nat_r_lo - nat_r_lo * nat_r_lo / (m * 2 ^ 86)) <
    x_hi_1 * 2 ^ 256 + x_lo_1 := by
  -- ======== Base case bounds ========
  have hbc := model_cbrtBaseCase_evm_correct x_hi_1 hxhi_lo hxhi_hi
  simp only at hbc
  rw [show icbrt (x_hi_1 / 4) = m from hm_eq.symm] at hbc
  have hm_lo : 2 ^ 83 ≤ m := hbc.2.2.2.1
  have hm_hi : m < 2 ^ 85 := hbc.2.2.2.2.1
  have hcube_le_w : m * m * m ≤ x_hi_1 / 4 := hbc.2.2.2.2.2.1
  have hm_wm : m < WORD_MOD := hbc.2.2.2.2.2.2.2.1
  have hm_pos : 2 ≤ m := Nat.le_trans (show 2 ≤ 2 ^ 83 from by
    rw [show (2 : Nat) ^ 83 = 2 * 2 ^ 82 from by
      rw [show (83 : Nat) = 1 + 82 from rfl, Nat.pow_add]]; omega) hm_lo
  have hR_pos : 0 < m * 2 ^ 86 := by omega
  have hd_pos : 0 < 3 * (m * m) :=
    Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega))
  have hres_bound : x_hi_1 / 4 - m * m * m ≤ 3 * (m * m) + 3 * m := hbc.2.2.2.2.2.2.1
  have hlimb_86 : (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172 < 2 ^ 86 := by
    have : x_hi_1 % 4 < 4 := Nat.mod_lt _ (by omega)
    have : x_lo_1 / 2 ^ 172 < 2 ^ 84 := by unfold WORD_MOD at hxlo; omega
    omega
  have hr_lo_bound : nat_r_lo < 2 ^ 87 := by
    rw [hr_lo_eq, Nat.div_lt_iff_lt_mul hd_pos]
    have h2m : 2 * m ≤ m * m := Nat.mul_le_mul_right m (by omega)
    calc ((x_hi_1 / 4 - m * m * m) * 2 ^ 86 +
            (x_hi_1 % 4 * 2 ^ 84 + x_lo_1 / 2 ^ 172))
        < ((x_hi_1 / 4 - m * m * m) + 1) * 2 ^ 86 := by omega
      _ ≤ (3 * (m * m) + 3 * m + 1) * 2 ^ 86 := by apply Nat.mul_le_mul_right; omega
      _ ≤ (2 * (3 * (m * m))) * 2 ^ 86 := by apply Nat.mul_le_mul_right; omega
      _ = 2 ^ 87 * (3 * (m * m)) := by
          rw [show (2 : Nat) ^ 87 = 2 * 2 ^ 86 from by
            rw [show (87 : Nat) = 1 + 86 from rfl, Nat.pow_add]]; omega
  have hr_lo_wm : nat_r_lo < WORD_MOD := by unfold WORD_MOD; omega
  have hmm_hi : m * m < 2 ^ 170 :=
    calc m * m < m * 2 ^ 85 := Nat.mul_lt_mul_of_pos_left hm_hi (by omega)
      _ ≤ 2 ^ 85 * 2 ^ 85 := Nat.mul_le_mul_right _ (Nat.le_of_lt hm_hi)
      _ = 2 ^ 170 := by rw [← Nat.pow_add]
  have hd_wm : 3 * (m * m) < WORD_MOD := by unfold WORD_MOD; omega
  have hrem_wm : nat_rem < WORD_MOD := by
    rw [hrem_eq]; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hd_pos) (Nat.le_of_lt hd_wm)
  have hc_gt1 : nat_r_lo * nat_r_lo / (m * 2 ^ 86) > 1 := by
    by_cases hcgt : nat_r_lo * nat_r_lo / (m * 2 ^ 86) > 1
    · exact hcgt
    · exfalso
      have hexact := model_cbrtQuadraticCorrection_evm_exact_when_c_le1
          m nat_r_lo nat_rem hm_wm hr_lo_wm hrem_wm hm_pos hm_hi hr_lo_bound (by omega)
      omega
  -- ======== Abbreviate ========
  let R := m * 2 ^ 86
  let c := nat_r_lo * nat_r_lo / R
  let ε := nat_r_lo * nat_r_lo % R
  let t := nat_r_lo - c
  -- ======== c ≤ nat_r_lo ========
  have hc_le : c ≤ nat_r_lo := by
    show nat_r_lo * nat_r_lo / (m * 2 ^ 86) ≤ nat_r_lo
    have hR_gt : nat_r_lo < m * 2 ^ 86 := by omega
    cases Nat.eq_or_lt_of_le (Nat.zero_le nat_r_lo) with
    | inl h => rw [← h]; simp
    | inr h =>
      exact Nat.le_of_lt ((Nat.div_lt_iff_lt_mul hR_pos).mpr
        (Nat.mul_lt_mul_of_pos_left hR_gt h))
  -- ======== Undershoot: ε * 3 * R ≤ nat_rem * 2^172 ========
  have hundershoot := undershoot_implies_rem_gt_3Reps m nat_r_lo nat_rem
      hm_wm hr_lo_wm hrem_wm hm_pos hm_hi hr_lo_bound hc_gt1 hr1_eq
  -- ======== x_norm decomposition ========
  have hx_decomp := x_norm_decomp x_hi_1 x_lo_1 (m * m * m) hcube_le_w
  have hn_full := Nat.div_add_mod
      ((x_hi_1 / 4 - m * m * m) * 2 ^ 86 +
        (x_hi_1 % 4 * 2 ^ 84 + x_lo_1 / 2 ^ 172)) (3 * (m * m))
  have h_num_eq : (x_hi_1 / 4 - m * m * m) * 2 ^ 86 +
      (x_hi_1 % 4 * 2 ^ 84 + x_lo_1 / 2 ^ 172) =
      3 * (m * m) * nat_r_lo + nat_rem := by
    rw [hr_lo_eq, hrem_eq]; exact hn_full.symm
  have hR3 := R_cube_factor m
  have hd_eq_3R2 := d_pow172_eq_3R_sq m
  -- x_norm lower bound: x_norm ≥ R³ + 3R²·r_lo (same as sub-lemma B)
  have hx_lb : m * m * m * 2 ^ 258 + 3 * (m * m) * nat_r_lo * 2 ^ 172 ≤
      x_hi_1 * 2 ^ 256 + x_lo_1 := by
    rw [hx_decomp, h_num_eq, Nat.add_mul, Nat.mul_assoc]; omega
  have hx_lb2 : R * R * R + 3 * (R * R) * nat_r_lo ≤ x_hi_1 * 2 ^ 256 + x_lo_1 := by
    calc R * R * R + 3 * (R * R) * nat_r_lo
        = m * m * m * 2 ^ 258 + 3 * (m * m) * nat_r_lo * 2 ^ 172 := by
          rw [← hR3]
          show R * R * R + 3 * (R * R) * nat_r_lo =
            R * R * R + 3 * (m * m) * nat_r_lo * 2 ^ 172
          rw [← hd_eq_3R2]
          simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ x_hi_1 * 2 ^ 256 + x_lo_1 := hx_lb
  -- ======== Division/mod identity ========
  have hdm := Nat.div_add_mod (nat_r_lo * nat_r_lo) R
  -- ======== Floor division bound: r_lo² < (c+1)R ========
  have hcR_lt : nat_r_lo * nat_r_lo < (c + 1) * R := by
    show nat_r_lo * nat_r_lo < (nat_r_lo * nat_r_lo / R + 1) * R
    have hmod_lt := Nat.mod_lt (nat_r_lo * nat_r_lo) hR_pos
    calc nat_r_lo * nat_r_lo
        = R * (nat_r_lo * nat_r_lo / R) + nat_r_lo * nat_r_lo % R := hdm.symm
      _ < R * (nat_r_lo * nat_r_lo / R) + R := Nat.add_lt_add_left hmod_lt _
      _ = R * (nat_r_lo * nat_r_lo / R + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = (nat_r_lo * nat_r_lo / R + 1) * R := Nat.mul_comm _ _
  -- t ≤ r_lo, t² ≤ r_lo² < (c+1)R
  have ht_le : t ≤ nat_r_lo := Nat.sub_le _ _
  have ht_sq_lt : t * t < (c + 1) * R :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul ht_le ht_le) hcR_lt
  -- ======== t³ < 6Rtc + 3Rc² ========
  have h_t_cube_lt : t * t * t < 6 * R * t * c + 3 * R * (c * c) := by
    cases Nat.eq_or_lt_of_le (Nat.zero_le t) with
    | inl ht0 =>
      rw [← ht0]; simp
      have hc_pos : 0 < c := Nat.lt_trans (by omega : 0 < 1) hc_gt1
      exact Nat.mul_pos (Nat.mul_pos (by omega : 0 < 3) hR_pos)
        (Nat.mul_pos hc_pos hc_pos)
    | inr ht_pos =>
      have h1 : t * (t * t) < t * ((c + 1) * R) :=
        Nat.mul_lt_mul_of_pos_left ht_sq_lt ht_pos
      rw [show t * t * t = t * (t * t) from Nat.mul_assoc _ _ _]
      calc t * (t * t)
          < t * ((c + 1) * R) := h1
        _ ≤ t * (6 * c * R) := by
            apply Nat.mul_le_mul_left
            -- (c + 1) * R ≤ (6 * c) * R
            exact Nat.mul_le_mul_right R (show c + 1 ≤ 6 * c from by
              have : c > 1 := hc_gt1; omega)
        _ = 6 * R * t * c := by
            suffices h : (↑(t * (6 * c * R)) : Int) = ↑(6 * R * t * c) by exact_mod_cast h
            push_cast; simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
        _ ≤ 6 * R * t * c + 3 * R * (c * c) := Nat.le_add_right _ _
  -- ======== 3Rt² + 6Rtc + 3Rc² = 3R·r_lo² (from sq_sum_expand) ========
  have htc_rlo : t + c = nat_r_lo := by show nat_r_lo - c + c = nat_r_lo; omega
  have hrlo_sq := sq_sum_expand t c
  have h3R_expand : 3 * R * (t * t) + (6 * R * t * c + 3 * R * (c * c)) =
      3 * R * (nat_r_lo * nat_r_lo) := by
    rw [← htc_rlo, hrlo_sq]
    suffices h : (↑(3 * R * (t * t) + (6 * R * t * c + 3 * R * (c * c))) : Int) =
        ↑(3 * R * (t * t + 2 * t * c + c * c)) by
      have h2 : (↑(3 * R * (t * t + 2 * t * c + c * c)) : Int) =
          ↑(3 * R * (t * t) + (6 * R * t * c + 3 * R * (c * c))) := h.symm
      exact_mod_cast h2.symm
    push_cast
    simp [Int.mul_add, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  -- ======== 3R²c + rem·2^172 ≥ 3R·r_lo² (from undershoot + div_add_mod) ========
  have h3R_rlo2 : 3 * (R * R) * c + ε * 3 * R = 3 * R * (nat_r_lo * nat_r_lo) := by
    -- 3R²c + 3Rε = 3R(Rc + ε) = 3R·r_lo²
    have h_factor : 3 * (R * R) * c + ε * 3 * R = 3 * R * (R * c + ε) := by
      suffices h : (↑(3 * (R * R) * c + ε * 3 * R) : Int) = ↑(3 * R * (R * c + ε)) by
        exact_mod_cast h
      push_cast
      simp only [Int.mul_add, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    rw [h_factor, show R * c + ε = nat_r_lo * nat_r_lo from hdm]
  have h_dom : 3 * R * (nat_r_lo * nat_r_lo) ≤
      3 * (R * R) * c + nat_rem * 2 ^ 172 := by
    calc 3 * R * (nat_r_lo * nat_r_lo)
        = 3 * (R * R) * c + ε * 3 * R := h3R_rlo2.symm
      _ ≤ 3 * (R * R) * c + nat_rem * 2 ^ 172 := Nat.add_le_add_left hundershoot _
  -- ======== Final chain: (R+t)³ < x_norm ========
  -- Goal: (m*2^86 + nat_r_lo - c)³ < x_norm.
  -- Since R, c, t are let-bound, goal is (R + nat_r_lo - c)³ < x_norm,
  -- which is definitionally (R + t + c - c)... we use Nat.add_sub_cancel:
  -- R + nat_r_lo - c = R + (nat_r_lo - c) = R + t (via hc_le and omega)
  -- Suffices: (R + t)³ < x_norm
  -- (R + t)³ = R³ + 3R²t + 3Rt² + t³  [cube_sum_expand]
  -- From algebraic chain + undershoot:
  --   3Rt² + t³ < 3R·r_lo² ≤ 3R²c + rem·2^172 ≤ 3R²r_lo  (NOT what I need)
  -- Actually: 3Rt² + t³ < 3R·r_lo² ≤ 3R²c + rem·2^172 (from h_dom)
  -- So: (R + t)³ = R³ + 3R²t + 3Rt² + t³ < R³ + 3R²t + 3R²c + rem·2^172
  --             = R³ + 3R²(t + c) + rem·2^172 = R³ + 3R²·r_lo + rem·2^172
  --             ≤ x_norm (from hx_lb2, which drops rem·2^172 and c_tail)
  -- WAIT: hx_lb2 only gives R³ + 3R²·r_lo ≤ x_norm. I need a bound with rem·2^172.
  -- BUT: 3Rt² + t³ < 3R²c + rem·2^172, and I also need ≤ 3R²·r_lo.
  --   3R²c ≤ 3R²·r_lo (since c ≤ r_lo). So 3Rt² + t³ < 3R²·r_lo + rem·2^172.
  --   Then: (R+t)³ < R³ + 3R²t + 3R²·r_lo + rem·2^172 ≤ R³ + 3R²·(t + r_lo) + rem...
  --   Hmm, this gives 3R²(t + r_lo), not 3R²·r_lo. Let me reconsider.
  --
  -- Correct chain: (R+t)³ = R³ + 3R²t + 3Rt² + t³
  -- Need to show < x_norm.
  -- x_norm ≥ R³ + 3R²·r_lo (from hx_lb2).
  -- Suffices: 3R²t + 3Rt² + t³ < 3R²·r_lo, i.e., 3Rt² + t³ < 3R²(r_lo - t) = 3R²c.
  -- But 3Rt² + t³ < 3R²c is NOT always true (as analyzed).
  -- The correct approach: use x_norm ≥ R³ + 3R²·r_lo + rem·2^172 (with rem term).
  -- But hx_lb2 drops the rem term.
  -- Need a TIGHTER lower bound: hx_lb (line above) gives m³·2^258 + 3m²·r_lo·2^172 ≤ x_norm.
  -- Which is R³ + 3R²·r_lo ≤ x_norm. No rem term.
  -- For the full bound, need: x_norm = R³ + 3R²r_lo + rem·2^172 + c_tail.
  -- But proving this exact equality through R-based terms was the problem.
  --
  -- Alternative: prove the FULL lower bound including rem*2^172:
  -- x_norm ≥ R³ + 3R²r_lo + rem*2^172
  -- From hx_decomp + h_num_eq: x_norm = m³·2^258 + (3m²·r_lo + rem)·2^172 + c_tail
  --   ≥ m³·2^258 + (3m²·r_lo + rem)·2^172
  --   = m³·2^258 + 3m²·r_lo·2^172 + rem·2^172
  --   = R³ + 3R²·r_lo + rem·2^172 (converting via hR3, hd_eq_3R2)
  have hx_lb3 : R * R * R + 3 * (R * R) * nat_r_lo + nat_rem * 2 ^ 172 ≤
      x_hi_1 * 2 ^ 256 + x_lo_1 := by
    have hx_lb_m : m * m * m * 2 ^ 258 + 3 * (m * m) * nat_r_lo * 2 ^ 172 +
        nat_rem * 2 ^ 172 ≤ x_hi_1 * 2 ^ 256 + x_lo_1 := by
      rw [hx_decomp, h_num_eq, Nat.add_mul, Nat.mul_assoc]; omega
    have h3R2rlo : 3 * (R * R) * nat_r_lo = 3 * (m * m) * nat_r_lo * 2 ^ 172 := by
      show 3 * (m * 2 ^ 86 * (m * 2 ^ 86)) * nat_r_lo =
        3 * (m * m) * nat_r_lo * 2 ^ 172
      rw [← hd_eq_3R2]; simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    calc R * R * R + 3 * (R * R) * nat_r_lo + nat_rem * 2 ^ 172
        = m * m * m * 2 ^ 258 + 3 * (m * m) * nat_r_lo * 2 ^ 172 +
            nat_rem * 2 ^ 172 := by rw [hR3, h3R2rlo]
      _ ≤ x_hi_1 * 2 ^ 256 + x_lo_1 := hx_lb_m
  -- Now the final chain works:
  -- (R + t)³ = R³ + 3R²t + 3Rt² + t³
  -- 3Rt² + t³ < 3R·r_lo² ≤ 3R²c + rem·2^172
  -- So (R+t)³ < R³ + 3R²t + 3R²c + rem·2^172 = R³ + 3R²·r_lo + rem·2^172 ≤ x_norm
  -- Use: R + nat_r_lo - c = R + t (definitionally, omega handles Nat sub)
  show (R + nat_r_lo - c) * (R + nat_r_lo - c) * (R + nat_r_lo - c) <
      x_hi_1 * 2 ^ 256 + x_lo_1
  have hrqc_eq : R + nat_r_lo - c = R + t := by omega
  rw [hrqc_eq, cube_sum_expand R t]
  calc R * R * R + 3 * (R * R) * t + 3 * R * (t * t) + t * t * t
      = R * R * R + 3 * (R * R) * t + (3 * R * (t * t) + t * t * t) := by omega
    _ < R * R * R + 3 * (R * R) * t + (3 * (R * R) * c + nat_rem * 2 ^ 172) := by
        -- Need: 3Rt² + t³ < 3R²c + rem·2^172
        -- Chain: 3Rt² + t³ < 3R·r_lo² ≤ 3R²c + rem·2^172
        have : 3 * R * (t * t) + t * t * t < 3 * R * (nat_r_lo * nat_r_lo) := by
          calc 3 * R * (t * t) + t * t * t
              < 3 * R * (t * t) + (6 * R * t * c + 3 * R * (c * c)) := by omega
            _ = 3 * R * (nat_r_lo * nat_r_lo) := h3R_expand
        omega
    _ = R * R * R + (3 * (R * R) * t + 3 * (R * R) * c) + nat_rem * 2 ^ 172 := by omega
    _ = R * R * R + 3 * (R * R) * (t + c) + nat_rem * 2 ^ 172 := by rw [← Nat.mul_add]
    _ = R * R * R + 3 * (R * R) * nat_r_lo + nat_rem * 2 ^ 172 := by rw [htc_rlo]
    _ ≤ x_hi_1 * 2 ^ 256 + x_lo_1 := hx_lb3

-- ============================================================================
-- ============================================================================
-- Undershoot algebraic core: r_qc³ < x_norm when undershoot fires
-- ============================================================================

/-- When the QC model returns r_qc + 1 (undershoot correction applied),
    then r_qc³ < x_norm and (r_qc+1)³ < WORD_MOD². -/
theorem qc_undershoot_cube_lt (x_hi_1 x_lo_1 : Nat)
    (hxhi_lo : 2 ^ 253 ≤ x_hi_1) (hxhi_hi : x_hi_1 < WORD_MOD)
    (hxlo : x_lo_1 < WORD_MOD)
    (m : Nat) (hm_eq : m = icbrt (x_hi_1 / 4))
    (nat_r_lo nat_rem : Nat)
    (hr_lo_eq : nat_r_lo = ((x_hi_1 / 4 - m * m * m) * 2 ^ 86 +
        (x_hi_1 % 4 * 2 ^ 84 + x_lo_1 / 2 ^ 172)) / (3 * (m * m)))
    (hrem_eq : nat_rem = ((x_hi_1 / 4 - m * m * m) * 2 ^ 86 +
        (x_hi_1 % 4 * 2 ^ 84 + x_lo_1 / 2 ^ 172)) % (3 * (m * m)))
    (hr1_eq : model_cbrtQuadraticCorrection_evm m nat_r_lo nat_rem =
        m * 2 ^ 86 + nat_r_lo - nat_r_lo * nat_r_lo / (m * 2 ^ 86) + 1) :
    let r_qc := m * 2 ^ 86 + nat_r_lo - nat_r_lo * nat_r_lo / (m * 2 ^ 86)
    r_qc * r_qc * r_qc < x_hi_1 * 2 ^ 256 + x_lo_1 ∧
    (r_qc + 1) * (r_qc + 1) * (r_qc + 1) < WORD_MOD * WORD_MOD := by
  simp only
  -- ======== Base case bounds ========
  have hbc := model_cbrtBaseCase_evm_correct x_hi_1 hxhi_lo hxhi_hi
  simp only at hbc
  rw [show icbrt (x_hi_1 / 4) = m from hm_eq.symm] at hbc
  have hm_lo : 2 ^ 83 ≤ m := hbc.2.2.2.1
  have hm_hi : m < 2 ^ 85 := hbc.2.2.2.2.1
  have hcube_le_w : m * m * m ≤ x_hi_1 / 4 := hbc.2.2.2.2.2.1
  have hm_wm : m < WORD_MOD := hbc.2.2.2.2.2.2.2.1
  have hm_pos : 2 ≤ m := Nat.le_trans (show 2 ≤ 2 ^ 83 from by
    rw [show (2 : Nat) ^ 83 = 2 * 2 ^ 82 from by
      rw [show (83 : Nat) = 1 + 82 from rfl, Nat.pow_add]]; omega) hm_lo
  have hR_pos : 0 < m * 2 ^ 86 := by omega
  have hd_pos : 0 < 3 * (m * m) :=
    Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega))
  -- ======== r_lo and rem bounds ========
  have hres_bound : x_hi_1 / 4 - m * m * m ≤ 3 * (m * m) + 3 * m := hbc.2.2.2.2.2.2.1
  have h2m : 2 * m ≤ m * m := Nat.mul_le_mul_right m (by omega)
  have hlimb_86 : (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172 < 2 ^ 86 := by
    have : x_hi_1 % 4 < 4 := Nat.mod_lt _ (by omega)
    have : x_lo_1 / 2 ^ 172 < 2 ^ 84 := by unfold WORD_MOD at hxlo; omega
    omega
  have hr_lo_bound : nat_r_lo < 2 ^ 87 := by
    rw [hr_lo_eq, Nat.div_lt_iff_lt_mul hd_pos]
    calc ((x_hi_1 / 4 - m * m * m) * 2 ^ 86 +
            (x_hi_1 % 4 * 2 ^ 84 + x_lo_1 / 2 ^ 172))
        < ((x_hi_1 / 4 - m * m * m) + 1) * 2 ^ 86 := by omega
      _ ≤ (3 * (m * m) + 3 * m + 1) * 2 ^ 86 := by apply Nat.mul_le_mul_right; omega
      _ ≤ (2 * (3 * (m * m))) * 2 ^ 86 := by apply Nat.mul_le_mul_right; omega
      _ = 2 ^ 87 * (3 * (m * m)) := by
          rw [show (2 : Nat) ^ 87 = 2 * 2 ^ 86 from by
            rw [show (87 : Nat) = 1 + 86 from rfl, Nat.pow_add]]; omega
  have hr_lo_wm : nat_r_lo < WORD_MOD := by unfold WORD_MOD; omega
  have hmm_hi : m * m < 2 ^ 170 :=
    calc m * m < m * 2 ^ 85 := Nat.mul_lt_mul_of_pos_left hm_hi (by omega)
      _ ≤ 2 ^ 85 * 2 ^ 85 := Nat.mul_le_mul_right _ (Nat.le_of_lt hm_hi)
      _ = 2 ^ 170 := by rw [← Nat.pow_add]
  have hd_wm : 3 * (m * m) < WORD_MOD := by unfold WORD_MOD; omega
  have hrem_wm : nat_rem < WORD_MOD := by
    rw [hrem_eq]; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hd_pos) (Nat.le_of_lt hd_wm)
  -- ======== Extract c > 1 ========
  have hc_gt1 : nat_r_lo * nat_r_lo / (m * 2 ^ 86) > 1 := by
    by_cases hcgt : nat_r_lo * nat_r_lo / (m * 2 ^ 86) > 1
    · exact hcgt
    · exfalso
      have hexact := model_cbrtQuadraticCorrection_evm_exact_when_c_le1
          m nat_r_lo nat_rem hm_wm hr_lo_wm hrem_wm hm_pos hm_hi hr_lo_bound (by omega)
      omega
  -- ======== r_qc ≤ R_MAX ========
  have hE1 := r_qc_le_r_max x_hi_1 x_lo_1 hxhi_lo hxhi_hi hxlo
  simp only at hE1
  rw [show icbrt (x_hi_1 / 4) = m from hm_eq.symm,
      show ((x_hi_1 / 4 - m * m * m) * 2 ^ 86 +
        (x_hi_1 % 4 * 2 ^ 84 + x_lo_1 / 2 ^ 172)) / (3 * (m * m)) = nat_r_lo
      from hr_lo_eq.symm] at hE1
  constructor
  · -- Conjunct 1: r_qc³ < x_norm
    -- Delegated to r_qc_cube_lt_x_norm helper lemma
    exact r_qc_cube_lt_x_norm x_hi_1 x_lo_1 hxhi_lo hxhi_hi hxlo
        m hm_eq nat_r_lo nat_rem hr_lo_eq hrem_eq hr1_eq
  · -- Conjunct 2: (r_qc+1)³ < WORD_MOD²
    -- From r_plus_rlo_le_rmax_succ: R + r_lo ≤ R_MAX + 1.
    -- From c ≥ 2: r_qc + 1 = R + r_lo - c + 1 ≤ R_MAX + 1 - 2 + 1 = R_MAX.
    -- Then (r_qc+1)³ ≤ R_MAX³ < WORD_MOD².
    have hRrlo := r_plus_rlo_le_rmax_succ x_hi_1 x_lo_1 hxhi_lo hxhi_hi hxlo
    simp only at hRrlo
    rw [show icbrt (x_hi_1 / 4) = m from hm_eq.symm,
        show ((x_hi_1 / 4 - m * m * m) * 2 ^ 86 +
          (x_hi_1 % 4 * 2 ^ 84 + x_lo_1 / 2 ^ 172)) / (3 * (m * m)) = nat_r_lo
        from hr_lo_eq.symm] at hRrlo
    -- hRrlo : m * 2^86 + nat_r_lo ≤ R_MAX + 1
    -- hc_gt1 : c > 1, i.e., c ≥ 2
    -- Goal: (R + r_lo - c + 1)³ < WORD_MOD²
    -- First show r_qc + 1 ≤ R_MAX via omega (c ≥ 2 and R + r_lo ≤ R_MAX + 1)
    have hrqc_succ_le : m * 2 ^ 86 + nat_r_lo -
        nat_r_lo * nat_r_lo / (m * 2 ^ 86) + 1 ≤ R_MAX := by omega
    exact Nat.lt_of_le_of_lt (cube_monotone hrqc_succ_le) r_max_cube_lt_wm2

-- ============================================================================
-- Full composition within 1 ulp
-- ============================================================================

/-- After base case + Karatsuba + quadratic correction, the result is within 1 of
    icbrt(x_norm) where x_norm = x_hi_1 * 2^256 + x_lo_1. -/
theorem composition_within_1ulp (x_hi_1 x_lo_1 : Nat)
    (hxhi_lo : 2 ^ 253 ≤ x_hi_1) (hxhi_hi : x_hi_1 < WORD_MOD)
    (hxlo : x_lo_1 < WORD_MOD) :
    let x_norm := x_hi_1 * 2 ^ 256 + x_lo_1
    let w := x_hi_1 / 4
    let m := icbrt w  -- r_hi after base case
    let res := w - m * m * m
    let d := 3 * (m * m)
    let limb_hi := (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172
    let r_lo := (res * 2 ^ 86 + limb_hi) / d
    let R := m * 2 ^ 86
    let correction := r_lo * r_lo / R
    let r_qc := R + r_lo - correction
    icbrt x_norm ≤ r_qc + 1 ∧ r_qc ≤ icbrt x_norm + 1 ∧
    r_qc < WORD_MOD ∧
    r_qc * r_qc * r_qc < WORD_MOD * WORD_MOD ∧
    r_qc + 1 < WORD_MOD ∧
    (r_qc * r_qc * r_qc > x_norm →
      icbrt x_norm * icbrt x_norm * icbrt x_norm < x_norm) := by
  -- Core properties from r_qc_properties (within 1 ulp + cube bound + overshoot)
  have h_props := r_qc_properties x_hi_1 x_lo_1 hxhi_lo hxhi_hi hxlo
  -- Range bound from r_qc_lt_pow172 (r_qc < 2^172)
  have h_bound := r_qc_lt_pow172 x_hi_1 x_lo_1 hxhi_lo hxhi_hi hxlo
  -- Unfold let-bindings so omega can see through them
  simp only at h_props h_bound ⊢
  refine ⟨h_props.1, h_props.2.1, ?_, h_props.2.2.1, ?_, h_props.2.2.2⟩
  · -- [3] r_qc < WORD_MOD: from h_bound (r_qc < 2^172 < WORD_MOD)
    unfold WORD_MOD; omega
  · -- [5] r_qc + 1 < WORD_MOD: from h_bound
    unfold WORD_MOD; omega

-- ============================================================================
-- P2 helper (c > 1, check = 0): (r_qc + 1)³ > x_norm
-- ============================================================================

set_option exponentiation.threshold 1024 in
/-- When c > 1 and the QC model returns r_qc (no undershoot correction),
    then (r_qc + 1)³ > x_norm, assuming the standalone QC bridge has already
    produced the scaled remainder bound.

    This isolates the remaining work to the algebraic phase:
    compare x_norm with (R + s)³ once rem·2^172 has been reduced to
    3R(ε + R - m²). -/
theorem r_qc_succ1_cube_gt_when_c_gt1_of_rem_bound (x_hi_1 x_lo_1 : Nat)
    (hxhi_lo : 2 ^ 253 ≤ x_hi_1) (hxhi_hi : x_hi_1 < WORD_MOD)
    (hxlo : x_lo_1 < WORD_MOD)
    (m : Nat) (hm_eq : m = icbrt (x_hi_1 / 4))
    (nat_r_lo nat_rem : Nat)
    (hr_lo_eq : nat_r_lo = ((x_hi_1 / 4 - m * m * m) * 2 ^ 86 +
        (x_hi_1 % 4 * 2 ^ 84 + x_lo_1 / 2 ^ 172)) / (3 * (m * m)))
    (hrem_eq : nat_rem = ((x_hi_1 / 4 - m * m * m) * 2 ^ 86 +
        (x_hi_1 % 4 * 2 ^ 84 + x_lo_1 / 2 ^ 172)) % (3 * (m * m)))
    (hc_gt1 : nat_r_lo * nat_r_lo / (m * 2 ^ 86) > 1)
    (hrem_bound_bridge :
        nat_rem * 2 ^ 172 ≤
          3 * (m * 2 ^ 86) * (nat_r_lo * nat_r_lo % (m * 2 ^ 86) + m * 2 ^ 86 - m * m)) :
    x_hi_1 * 2 ^ 256 + x_lo_1 <
      (m * 2 ^ 86 + nat_r_lo - nat_r_lo * nat_r_lo / (m * 2 ^ 86) + 1) *
      (m * 2 ^ 86 + nat_r_lo - nat_r_lo * nat_r_lo / (m * 2 ^ 86) + 1) *
      (m * 2 ^ 86 + nat_r_lo - nat_r_lo * nat_r_lo / (m * 2 ^ 86) + 1) := by
  -- ======== Base case bounds ========
  have hbc := model_cbrtBaseCase_evm_correct x_hi_1 hxhi_lo hxhi_hi
  simp only at hbc
  rw [show icbrt (x_hi_1 / 4) = m from hm_eq.symm] at hbc
  have hm_lo : 2 ^ 83 ≤ m := hbc.2.2.2.1
  have hm_hi : m < 2 ^ 85 := hbc.2.2.2.2.1
  have hcube_le_w : m * m * m ≤ x_hi_1 / 4 := hbc.2.2.2.2.2.1
  have hm_wm : m < WORD_MOD := hbc.2.2.2.2.2.2.2.1
  have hm_pos : 2 ≤ m := Nat.le_trans (show 2 ≤ 2 ^ 83 from by
    rw [show (2 : Nat) ^ 83 = 2 * 2 ^ 82 from by
      rw [show (83 : Nat) = 1 + 82 from rfl, Nat.pow_add]]; omega) hm_lo
  have hR_pos : 0 < m * 2 ^ 86 := by omega
  have hd_pos : 0 < 3 * (m * m) :=
    Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega))
  -- r_lo and rem bounds
  have hres_bound : x_hi_1 / 4 - m * m * m ≤ 3 * (m * m) + 3 * m := hbc.2.2.2.2.2.2.1
  have hlimb_86 : (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172 < 2 ^ 86 := by
    have : x_hi_1 % 4 < 4 := Nat.mod_lt _ (by omega)
    have : x_lo_1 / 2 ^ 172 < 2 ^ 84 := by unfold WORD_MOD at hxlo; omega
    omega
  have hr_lo_bound : nat_r_lo < 2 ^ 87 := by
    rw [hr_lo_eq, Nat.div_lt_iff_lt_mul hd_pos]
    have h2m : 2 * m ≤ m * m := Nat.mul_le_mul_right m (by omega)
    calc ((x_hi_1 / 4 - m * m * m) * 2 ^ 86 +
            (x_hi_1 % 4 * 2 ^ 84 + x_lo_1 / 2 ^ 172))
        < ((x_hi_1 / 4 - m * m * m) + 1) * 2 ^ 86 := by omega
      _ ≤ (3 * (m * m) + 3 * m + 1) * 2 ^ 86 := by apply Nat.mul_le_mul_right; omega
      _ ≤ (2 * (3 * (m * m))) * 2 ^ 86 := by apply Nat.mul_le_mul_right; omega
      _ = 2 ^ 87 * (3 * (m * m)) := by
          rw [show (2 : Nat) ^ 87 = 2 * 2 ^ 86 from by
            rw [show (87 : Nat) = 1 + 86 from rfl, Nat.pow_add]]; omega
  have hr_lo_wm : nat_r_lo < WORD_MOD := by unfold WORD_MOD; omega
  have hmm_hi : m * m < 2 ^ 170 :=
    calc m * m < m * 2 ^ 85 := Nat.mul_lt_mul_of_pos_left hm_hi (by omega)
      _ ≤ 2 ^ 85 * 2 ^ 85 := Nat.mul_le_mul_right _ (Nat.le_of_lt hm_hi)
      _ = 2 ^ 170 := by rw [← Nat.pow_add]
  have hd_wm : 3 * (m * m) < WORD_MOD := by unfold WORD_MOD; omega
  have hrem_wm : nat_rem < WORD_MOD := by
    rw [hrem_eq]; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hd_pos) (Nat.le_of_lt hd_wm)
  -- Abbreviate
  let R := m * 2 ^ 86
  let c := nat_r_lo * nat_r_lo / R
  let ε := nat_r_lo * nat_r_lo % R
  let d := 3 * (m * m)
  let s := nat_r_lo - c + 1
  let B := (c - 1) * (2 * nat_r_lo - c + 1)
  -- ======== Key bound: B < m² ========
  -- B = (c-1)(2r_lo-c+1) ≤ 2(c-1)r_lo < 2cr_lo < R (from 2cr_lo < R)
  have hR_ge : 2 ^ 169 ≤ R :=
    calc 2 ^ 169 = 2 ^ 83 * 2 ^ 86 := by rw [← Nat.pow_add]
      _ ≤ m * 2 ^ 86 := Nat.mul_le_mul_right _ hm_lo
  have hc_le : c ≤ nat_r_lo := by
    show nat_r_lo * nat_r_lo / R ≤ nat_r_lo
    cases Nat.eq_or_lt_of_le (Nat.zero_le nat_r_lo) with
    | inl h => rw [← h]; simp
    | inr h =>
      exact Nat.le_of_lt ((Nat.div_lt_iff_lt_mul hR_pos).mpr
        (Nat.mul_lt_mul_of_pos_left (by omega : nat_r_lo < R) h))
  have hcR_le : c * R ≤ nat_r_lo * nat_r_lo := Nat.div_mul_le_self _ _
  -- 2cr_lo < R (same as sub-lemma A)
  have hc_lt_32 : c < 32 := by
    have : c * R < 2 ^ 174 := Nat.lt_of_le_of_lt hcR_le
      (calc nat_r_lo * nat_r_lo
          ≤ nat_r_lo * 2 ^ 87 := Nat.mul_le_mul_left _ (Nat.le_of_lt hr_lo_bound)
        _ < 2 ^ 87 * 2 ^ 87 := Nat.mul_lt_mul_of_pos_right hr_lo_bound (Nat.two_pow_pos 87)
        _ = 2 ^ 174 := by rw [← Nat.pow_add])
    have h174 : (2 : Nat) ^ 174 = 32 * 2 ^ 169 := by
      rw [show (174 : Nat) = 5 + 169 from rfl, Nat.pow_add]
    by_cases hc0 : c = 0; · omega
    · exact Nat.lt_of_mul_lt_mul_right
        (calc c * R < 2 ^ 174 := ‹_›
          _ = 32 * 2 ^ 169 := h174
          _ ≤ 32 * R := Nat.mul_le_mul_left _ hR_ge)
  -- r_lo > 0 (from c ≥ 2 and c ≤ r_lo, and c > 1 means r_lo² ≥ 2R > 0 means r_lo > 0)
  have hr_lo_pos : 0 < nat_r_lo := by
    rcases Nat.eq_or_lt_of_le (Nat.zero_le nat_r_lo) with h | h
    · -- r_lo = 0: then c = 0, contradicting c > 1
      rw [← h] at hc_gt1; simp at hc_gt1
    · exact h
  have hcr_lt : c * nat_r_lo < 2 ^ 92 :=
    calc c * nat_r_lo < 32 * nat_r_lo := Nat.mul_lt_mul_of_pos_right hc_lt_32 hr_lo_pos
      _ ≤ 32 * 2 ^ 87 := Nat.mul_le_mul_left _ (Nat.le_of_lt hr_lo_bound)
      _ = 2 ^ 92 := by rw [show (32 : Nat) = 2 ^ 5 from rfl, ← Nat.pow_add]
  have h2cr : 2 * c * nat_r_lo < R := by
    calc 2 * c * nat_r_lo = 2 * (c * nat_r_lo) := Nat.mul_assoc 2 c nat_r_lo
      _ < 2 * 2 ^ 92 := Nat.mul_lt_mul_of_pos_left hcr_lt (by omega)
      _ = 2 ^ 93 := by rw [show (93 : Nat) = 1 + 92 from rfl, Nat.pow_add]
      _ ≤ R := Nat.le_trans (Nat.pow_le_pow_right (by omega) (by omega : 93 ≤ 169)) hR_ge
  have hrem_bound : nat_rem * 2 ^ 172 ≤ 3 * R * (ε + R - m * m) := by
    simpa [R, ε] using hrem_bound_bridge
  have hmm_lo : 2 ^ 166 ≤ m * m := by
    calc 2 ^ 166 = 2 ^ 83 * 2 ^ 83 := by rw [← Nat.pow_add]
      _ ≤ m * m := Nat.mul_le_mul hm_lo hm_lo
  have hc_ge2 : 2 ≤ c := hc_gt1
  have hB_lt_2cr : B < 2 * c * nat_r_lo := by
    show (c - 1) * (2 * nat_r_lo - c + 1) < 2 * c * nat_r_lo
    have hc_pos : 0 < c := by omega
    have h_inner : 2 * nat_r_lo - c + 1 < 2 * nat_r_lo := by omega
    calc (c - 1) * (2 * nat_r_lo - c + 1)
        ≤ c * (2 * nat_r_lo - c + 1) := Nat.mul_le_mul_right _ (by omega)
      _ < c * (2 * nat_r_lo) := Nat.mul_lt_mul_of_pos_left h_inner hc_pos
      _ = 2 * c * nat_r_lo := by
          simp only [Nat.mul_assoc, Nat.mul_comm]
  have h2cr_93 : 2 * c * nat_r_lo < 2 ^ 93 := by
    calc 2 * c * nat_r_lo
        = 2 * (c * nat_r_lo) := Nat.mul_assoc 2 c nat_r_lo
      _ < 2 * 2 ^ 92 := Nat.mul_lt_mul_of_pos_left hcr_lt (by omega)
      _ = 2 ^ 93 := by rw [show (93 : Nat) = 1 + 92 from rfl, Nat.pow_add]
  have hB_lt_93 : B < 2 ^ 93 := Nat.lt_trans hB_lt_2cr h2cr_93
  have hgap8 : 8 ≤ m * m - B := mm_sub_B_ge_eight m B hmm_lo hB_lt_93
  let c_tail := x_lo_1 % 2 ^ 172
  have hctail_lt : c_tail < 2 ^ 172 := by
    dsimp [c_tail]
    exact Nat.mod_lt _ (Nat.two_pow_pos 172)
  have htail_dom : 3 * R * B + c_tail < 3 * R * (m * m) := by
    exact tail_dom_by_mm_gap R (m * m) B c_tail hR_ge hgap8 hctail_lt
  have hx_decomp := x_norm_decomp x_hi_1 x_lo_1 (m * m * m) hcube_le_w
  have hn_full := Nat.div_add_mod
      ((x_hi_1 / 4 - m * m * m) * 2 ^ 86 +
        (x_hi_1 % 4 * 2 ^ 84 + x_lo_1 / 2 ^ 172)) (3 * (m * m))
  have h_num_eq : (x_hi_1 / 4 - m * m * m) * 2 ^ 86 +
      (x_hi_1 % 4 * 2 ^ 84 + x_lo_1 / 2 ^ 172) =
      3 * (m * m) * nat_r_lo + nat_rem := by
    rw [hr_lo_eq, hrem_eq]
    exact hn_full.symm
  have hR3 := R_cube_factor m
  have hd_eq_3R2 := d_pow172_eq_3R_sq m
  have hx_eq : x_hi_1 * 2 ^ 256 + x_lo_1 =
      R * R * R + 3 * (R * R) * nat_r_lo + nat_rem * 2 ^ 172 + c_tail := by
    calc x_hi_1 * 2 ^ 256 + x_lo_1
        = m * m * m * 2 ^ 258 + (3 * (m * m) * nat_r_lo + nat_rem) * 2 ^ 172 + c_tail := by
            simpa [c_tail] using hx_decomp.trans (by rw [h_num_eq])
      _ = m * m * m * 2 ^ 258 + 3 * (m * m) * nat_r_lo * 2 ^ 172 + nat_rem * 2 ^ 172 + c_tail := by
            rw [Nat.add_mul]
            omega
      _ = R * R * R + 3 * (R * R) * nat_r_lo + nat_rem * 2 ^ 172 + c_tail := by
            rw [← hR3]
            have h3R2rlo : 3 * (R * R) * nat_r_lo = 3 * (m * m) * nat_r_lo * 2 ^ 172 := by
              show 3 * (m * 2 ^ 86 * (m * 2 ^ 86)) * nat_r_lo =
                3 * (m * m) * nat_r_lo * 2 ^ 172
              rw [← hd_eq_3R2]
              simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
            rw [h3R2rlo]
  have hs_sum : s + (c - 1) = nat_r_lo := by
    simp only [s]
    omega
  have hdm : R * c + ε = nat_r_lo * nat_r_lo := by
    dsimp [c, ε]
    exact Nat.div_add_mod (nat_r_lo * nat_r_lo) R
  have hsq_B : B = 2 * s * (c - 1) + (c - 1) * (c - 1) := by
    dsimp [B]
    have hinner : 2 * nat_r_lo - c + 1 = 2 * s + (c - 1) := by
      rw [← hs_sum]
      omega
    rw [hinner]
    calc (c - 1) * (2 * s + (c - 1))
      _ = (c - 1) * (2 * s) + (c - 1) * (c - 1) := by rw [Nat.mul_add]
      _ = 2 * s * (c - 1) + (c - 1) * (c - 1) := by ac_rfl
  have hsq_gap : s * s + B = nat_r_lo * nat_r_lo := by
    have hsq := sq_sum_expand s (c - 1)
    rw [hs_sum] at hsq
    calc s * s + B = s * s + (2 * s * (c - 1) + (c - 1) * (c - 1)) := by rw [hsq_B]
      _ = nat_r_lo * nat_r_lo := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsq.symm
  have hm_le_86 : m ≤ 2 ^ 86 := Nat.le_trans (Nat.le_of_lt hm_hi)
    (Nat.pow_le_pow_right (by omega) (by omega : 85 ≤ 86))
  have hmm_le_epsR : m * m ≤ ε + R := by
    have hmm_le_R : m * m ≤ R := by
      dsimp [R]
      exact Nat.mul_le_mul_left _ hm_le_86
    omega
  have hRc : R * (c - 1) + R = R * c := by
    calc R * (c - 1) + R = R * (c - 1) + R * 1 := by rw [Nat.mul_one]
      _ = R * ((c - 1) + 1) := by rw [← Nat.mul_add]
      _ = R * c := by
          have : c - 1 + 1 = c := by omega
          rw [this]
  have hcore1 : R * nat_r_lo + ε + R = R * s + (R * c + ε) := by
    rw [← hs_sum, Nat.mul_add]
    calc R * s + R * (c - 1) + ε + R
        = R * s + (R * (c - 1) + R) + ε := by ac_rfl
      _ = R * s + R * c + ε := by rw [hRc]
      _ = R * s + (R * c + ε) := by ac_rfl
  have hcore :
      R * nat_r_lo + ε + R = R * s + (s * s + B) := by
    calc R * nat_r_lo + ε + R = R * s + (R * c + ε) := hcore1
      _ = R * s + nat_r_lo * nat_r_lo := by
          rw [hdm]
      _ = R * s + (s * s + B) := by
          rw [← hsq_gap]
  have halg :
      3 * (R * R) * nat_r_lo + 3 * R * (ε + R) =
      3 * (R * R) * s + 3 * R * (s * s + B) := by
    calc 3 * (R * R) * nat_r_lo + 3 * R * (ε + R)
        = 3 * R * (R * nat_r_lo) + 3 * R * ε + 3 * R * R := by
            rw [Nat.mul_add]
            ac_rfl
      _ = 3 * R * (R * nat_r_lo + ε + R) := by
            rw [Nat.mul_add, Nat.mul_add]
      _ = 3 * R * (R * s + (s * s + B)) := by rw [hcore]
      _ = 3 * (R * R) * s + 3 * R * (s * s + B) := by
            rw [Nat.mul_add]
            ac_rfl
  have hsplit : 3 * R * (s * s + B) = 3 * R * (s * s) + 3 * R * B := by
    rw [Nat.mul_add]
  have hsub_add :
      3 * R * (ε + R - m * m) + 3 * R * (m * m) = 3 * R * (ε + R) := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hmm_le_epsR]
  have hphase2_sum :
      (3 * (R * R) * nat_r_lo + 3 * R * (ε + R - m * m) + c_tail) + 3 * R * (m * m) =
      3 * (R * R) * s + 3 * R * (s * s) + (3 * R * B + c_tail) := by
    calc (3 * (R * R) * nat_r_lo + 3 * R * (ε + R - m * m) + c_tail) + 3 * R * (m * m)
        = 3 * (R * R) * nat_r_lo + (3 * R * (ε + R - m * m) + 3 * R * (m * m)) + c_tail := by
            ac_rfl
      _ = 3 * (R * R) * nat_r_lo + 3 * R * (ε + R) + c_tail := by rw [hsub_add]
      _ = 3 * (R * R) * s + 3 * R * (s * s) + (3 * R * B + c_tail) := by
            rw [halg, hsplit]
            ac_rfl
  have hphase2 :
      3 * (R * R) * nat_r_lo + 3 * R * (ε + R - m * m) + c_tail <
      3 * (R * R) * s + 3 * R * (s * s) := by
    have hsum_lt :
        (3 * (R * R) * nat_r_lo + 3 * R * (ε + R - m * m) + c_tail) + 3 * R * (m * m) <
        (3 * (R * R) * s + 3 * R * (s * s)) + 3 * R * (m * m) := by
      rw [hphase2_sum]
      exact Nat.add_lt_add_left htail_dom (3 * (R * R) * s + 3 * R * (s * s))
    exact Nat.lt_of_add_lt_add_right hsum_lt
  have hphase1 :
      3 * (R * R) * nat_r_lo + nat_rem * 2 ^ 172 + c_tail ≤
      3 * (R * R) * nat_r_lo + 3 * R * (ε + R - m * m) + c_tail := by
    exact Nat.add_le_add_right (Nat.add_le_add_left hrem_bound _) _
  have hupper :
      3 * (R * R) * nat_r_lo + nat_rem * 2 ^ 172 + c_tail <
      3 * (R * R) * s + 3 * R * (s * s) := by
    exact Nat.lt_of_le_of_lt hphase1 hphase2
  have hgoal : x_hi_1 * 2 ^ 256 + x_lo_1 < (R + s) * (R + s) * (R + s) := by
    calc x_hi_1 * 2 ^ 256 + x_lo_1
        = R * R * R + (3 * (R * R) * nat_r_lo + nat_rem * 2 ^ 172 + c_tail) := by
            rw [hx_eq]
            omega
      _ < R * R * R + (3 * (R * R) * s + 3 * R * (s * s)) := Nat.add_lt_add_left hupper _
      _ ≤ (R + s) * (R + s) * (R + s) := by
            rw [cube_sum_expand R s]
            omega
  have hsum : R + s = m * 2 ^ 86 + nat_r_lo - nat_r_lo * nat_r_lo / (m * 2 ^ 86) + 1 := by
    dsimp [R, s, c]
    rw [← Nat.add_assoc, ← Nat.add_sub_assoc hc_le]
  calc
    x_hi_1 * 2 ^ 256 + x_lo_1 < (R + s) * (R + s) * (R + s) := hgoal
    _ = (m * 2 ^ 86 + nat_r_lo - nat_r_lo * nat_r_lo / (m * 2 ^ 86) + 1) *
        (m * 2 ^ 86 + nat_r_lo - nat_r_lo * nat_r_lo / (m * 2 ^ 86) + 1) *
        (m * 2 ^ 86 + nat_r_lo - nat_r_lo * nat_r_lo / (m * 2 ^ 86) + 1) := by
          rw [hsum]

set_option exponentiation.threshold 1024 in
/-- When c > 1 and the QC model returns exactly r_qc, the standalone QC bridge
    supplies the remainder bound and the algebraic helper closes
    `(r_qc + 1)^3 > x_norm`. -/
theorem r_qc_succ1_cube_gt_when_c_gt1 (x_hi_1 x_lo_1 : Nat)
    (hxhi_lo : 2 ^ 253 ≤ x_hi_1) (hxhi_hi : x_hi_1 < WORD_MOD)
    (hxlo : x_lo_1 < WORD_MOD)
    (m : Nat) (hm_eq : m = icbrt (x_hi_1 / 4))
    (nat_r_lo nat_rem : Nat)
    (hr_lo_eq : nat_r_lo = ((x_hi_1 / 4 - m * m * m) * 2 ^ 86 +
        (x_hi_1 % 4 * 2 ^ 84 + x_lo_1 / 2 ^ 172)) / (3 * (m * m)))
    (hrem_eq : nat_rem = ((x_hi_1 / 4 - m * m * m) * 2 ^ 86 +
        (x_hi_1 % 4 * 2 ^ 84 + x_lo_1 / 2 ^ 172)) % (3 * (m * m)))
    (hc_gt1 : nat_r_lo * nat_r_lo / (m * 2 ^ 86) > 1)
    (hr1_eq : model_cbrtQuadraticCorrection_evm m nat_r_lo nat_rem =
        m * 2 ^ 86 + nat_r_lo - nat_r_lo * nat_r_lo / (m * 2 ^ 86)) :
    x_hi_1 * 2 ^ 256 + x_lo_1 <
      (m * 2 ^ 86 + nat_r_lo - nat_r_lo * nat_r_lo / (m * 2 ^ 86) + 1) *
      (m * 2 ^ 86 + nat_r_lo - nat_r_lo * nat_r_lo / (m * 2 ^ 86) + 1) *
      (m * 2 ^ 86 + nat_r_lo - nat_r_lo * nat_r_lo / (m * 2 ^ 86) + 1) := by
  have hbc := model_cbrtBaseCase_evm_correct x_hi_1 hxhi_lo hxhi_hi
  simp only at hbc
  rw [show icbrt (x_hi_1 / 4) = m from hm_eq.symm] at hbc
  have hm_lo : 2 ^ 83 ≤ m := hbc.2.2.2.1
  have hm_hi : m < 2 ^ 85 := hbc.2.2.2.2.1
  have hm_wm : m < WORD_MOD := hbc.2.2.2.2.2.2.2.1
  have hm_pos : 2 ≤ m := Nat.le_trans (show 2 ≤ 2 ^ 83 from by
    rw [show (2 : Nat) ^ 83 = 2 * 2 ^ 82 from by
      rw [show (83 : Nat) = 1 + 82 from rfl, Nat.pow_add]]
    omega) hm_lo
  have hd_pos : 0 < 3 * (m * m) :=
    Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega))
  have hres_bound : x_hi_1 / 4 - m * m * m ≤ 3 * (m * m) + 3 * m := hbc.2.2.2.2.2.2.1
  have hlimb_86 : (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172 < 2 ^ 86 := by
    have : x_hi_1 % 4 < 4 := Nat.mod_lt _ (by omega)
    have : x_lo_1 / 2 ^ 172 < 2 ^ 84 := by
      unfold WORD_MOD at hxlo
      omega
    omega
  have hr_lo_bound : nat_r_lo < 2 ^ 87 := by
    rw [hr_lo_eq, Nat.div_lt_iff_lt_mul hd_pos]
    have h2m : 2 * m ≤ m * m := Nat.mul_le_mul_right m (by omega)
    calc ((x_hi_1 / 4 - m * m * m) * 2 ^ 86 +
            (x_hi_1 % 4 * 2 ^ 84 + x_lo_1 / 2 ^ 172))
        < ((x_hi_1 / 4 - m * m * m) + 1) * 2 ^ 86 := by omega
      _ ≤ (3 * (m * m) + 3 * m + 1) * 2 ^ 86 := by
          apply Nat.mul_le_mul_right
          omega
      _ ≤ (2 * (3 * (m * m))) * 2 ^ 86 := by
          apply Nat.mul_le_mul_right
          omega
      _ = 2 ^ 87 * (3 * (m * m)) := by
          rw [show (2 : Nat) ^ 87 = 2 * 2 ^ 86 from by
            rw [show (87 : Nat) = 1 + 86 from rfl, Nat.pow_add]]
          omega
  have hr_lo_wm : nat_r_lo < WORD_MOD := by
    unfold WORD_MOD
    omega
  have hmm_hi : m * m < 2 ^ 170 :=
    calc m * m < m * 2 ^ 85 := Nat.mul_lt_mul_of_pos_left hm_hi (by omega)
      _ ≤ 2 ^ 85 * 2 ^ 85 := Nat.mul_le_mul_right _ (Nat.le_of_lt hm_hi)
      _ = 2 ^ 170 := by rw [← Nat.pow_add]
  have hd_wm : 3 * (m * m) < WORD_MOD := by
    have : 3 * (m * m) < 3 * 2 ^ 170 := Nat.mul_lt_mul_of_pos_left hmm_hi (by omega)
    unfold WORD_MOD
    omega
  have hrem_small : nat_rem < 3 * (m * m) := by
    rw [hrem_eq]
    exact Nat.mod_lt _ hd_pos
  have hrem_wm : nat_rem < WORD_MOD := Nat.lt_of_lt_of_le hrem_small (Nat.le_of_lt hd_wm)
  have hrem_bound_bridge :=
    model_cbrtQuadraticCorrection_evm_rem_bound_when_c_gt1_exact
      m nat_r_lo nat_rem hm_wm hr_lo_wm hrem_wm hm_pos hm_hi hr_lo_bound
      hrem_small hc_gt1 hr1_eq
  exact r_qc_succ1_cube_gt_when_c_gt1_of_rem_bound
    x_hi_1 x_lo_1 hxhi_lo hxhi_hi hxlo
    m hm_eq nat_r_lo nat_rem hr_lo_eq hrem_eq hc_gt1 hrem_bound_bridge

end Cbrt512Spec

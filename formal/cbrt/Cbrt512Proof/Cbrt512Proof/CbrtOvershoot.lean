/-
  Sub-lemma E2: When r_qc³ > x_norm (overshoot), x_norm is not a perfect cube.
  This ensures the cbrtUp wrapper's cube-and-compare correction is sound.
-/
import Cbrt512Proof.GeneratedCbrt512Model
import Cbrt512Proof.CbrtBaseCase
import Cbrt512Proof.CbrtAlgebraic
import Cbrt512Proof.CbrtSublemmaB
import Cbrt512Proof.EvmBridge
import CbrtProof.CbrtCorrect

namespace Cbrt512Spec

open Cbrt512GeneratedModel

-- ============================================================================
-- Sub-lemma E2: Overshoot implies not a perfect cube
-- ============================================================================

/-- When the algorithm overshoots (r_qc³ > x_norm), x_norm is not a perfect cube.
    From sub-lemmas A and B, r_qc = icbrt(x_norm) + 1 when r_qc³ > x_norm.
    If x_norm were a perfect cube s³, the Karatsuba quotient r_lo captures the
    exact linear correction and the quadratic correction c = ⌊r_lo²/R⌋ exactly
    compensates, yielding r_qc = s (no overshoot). -/

-- Helper: (t + delta)² ≥ delta * R when 3R²·delta ≤ 3Rt² + t³ (perfect cube constraint).
-- Case 1 (t² < 6R): cancel 3R from 3R²·delta < 3R(t²+2t) → R·delta < t²+2t ≤ (t+delta)².
-- Case 2 (t² ≥ 6R): multiply by 3R: 3R²·delta ≤ 3Rt² + t³ ≤ 3Rt² + 6Rt·delta ≤ 3R(t+delta)².
private theorem quad_correction_ge_delta (R t delta : Nat)
    (hR_lo : 2 ^ 169 ≤ R) (hdelta_pos : 0 < delta)
    (hcube_upper : 3 * (R * R) * delta ≤ 3 * R * (t * t) + t * t * t)
    (hcube_lower : 3 * R * (t * t) + t * t * t < 3 * (R * R) * delta + 3 * (R * R) + 2 ^ 172) :
    delta * R ≤ (t + delta) * (t + delta) := by
  have hR_pos : 0 < R := by omega
  by_cases ht_sq : t * t < 6 * R
  · -- Case 1: t² < 6R. If t = 0, hcube_upper forces delta = 0, contradiction.
    by_cases ht0 : t = 0
    · -- t = 0: 3R²·delta ≤ 0, contradiction
      exfalso
      have h1 : 0 < 3 * (R * R) * delta :=
        Nat.mul_pos (Nat.mul_pos (by omega) (Nat.mul_pos hR_pos hR_pos)) hdelta_pos
      rw [ht0, show (0 : Nat) * 0 = 0 from rfl, Nat.mul_zero, Nat.add_zero] at hcube_upper
      omega
    · -- t ≥ 1: t³ = t·t² < t·6R, so 3R²·delta < 3R(t²+2t), cancel 3R → R·delta < t²+2t
      have ht_pos : 0 < t := by omega
      have ht3_bound : t * t * t < 6 * R * t := by
        rw [show t * t * t = t * (t * t) from Nat.mul_assoc _ _ _,
            show 6 * R * t = t * (6 * R) from by
              simp only [Nat.mul_comm, Nat.mul_left_comm]]
        exact Nat.mul_lt_mul_of_pos_left ht_sq ht_pos
      -- 3R²·delta ≤ 3Rt² + t³ < 3Rt² + 6Rt = 3R(t² + 2t)
      have h_bound : 3 * (R * R) * delta < 3 * R * (t * t + 2 * t) := by
        have h6eq : 6 * R * t = 3 * R * (2 * t) := by
          simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        calc 3 * (R * R) * delta
            ≤ 3 * R * (t * t) + t * t * t := hcube_upper
          _ < 3 * R * (t * t) + 6 * R * t := by omega
          _ = 3 * R * (t * t) + 3 * R * (2 * t) := by rw [h6eq]
          _ = 3 * R * (t * t + 2 * t) := by rw [← Nat.mul_add]
      -- Cancel 3R: R·delta < t² + 2t
      have h_cancel : R * delta < t * t + 2 * t := by
        have h_assoc : 3 * (R * R) * delta = 3 * R * (R * delta) := by
          simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        rw [h_assoc] at h_bound
        exact Nat.lt_of_mul_lt_mul_left h_bound
      -- (t+delta)² = t² + 2t·delta + delta² ≥ t² + 2t ≥ R·delta + 1
      have h_sq_lb : t * t + 2 * t ≤ (t + delta) * (t + delta) := by
        rw [sq_sum_expand t delta]
        have : 2 * t ≤ 2 * t * delta := Nat.le_mul_of_pos_right _ hdelta_pos
        omega
      calc delta * R = R * delta := Nat.mul_comm _ _
        _ ≤ t * t + 2 * t := by omega
        _ ≤ (t + delta) * (t + delta) := h_sq_lb
  · -- Case 2: t² ≥ 6R. Strategy: show 3R²·delta ≤ 3R·(t+delta)² by t³ ≤ 6Rt·delta.
    have ht_sq_ge : 6 * R ≤ t * t := Nat.le_of_not_lt ht_sq
    have ht_pos : 0 < t := by
      cases Nat.eq_or_lt_of_le (Nat.zero_le t) with
      | inl h => rw [← h] at ht_sq_ge; omega
      | inr h => exact h
    -- 3R² > 2^172 (from R ≥ 2^169)
    have h3R2_gt : 2 ^ 172 ≤ 3 * (R * R) :=
      -- 2^172 ≤ 2^169 * R ≤ R * R ≤ 3*(R*R)
      Nat.le_trans
        (Nat.le_trans
          (show 2 ^ 172 ≤ 2 ^ 169 * R from
            calc 2 ^ 172 = 2 ^ 169 * 2 ^ 3 := by rw [← Nat.pow_add]
              _ ≤ 2 ^ 169 * R := Nat.mul_le_mul_left _ (by omega : 2 ^ 3 ≤ R))
          (Nat.mul_le_mul_right _ hR_lo))
        (Nat.le_mul_of_pos_left _ (by omega))
    -- t² < R·(delta+2): from 3Rt² ≤ 3Rt²+t³ < 3R²(delta+2) (since 2^172 < 3R²)
    have h_Rdelta2 : t * t < R * (delta + 2) := by
      have h_rhs : 3 * (R * R) * delta + 3 * (R * R) + 2 ^ 172 ≤
          3 * (R * R) * (delta + 2) := by
        rw [show 3 * (R * R) * (delta + 2) = 3 * (R * R) * delta + 3 * (R * R) * 2 from
          Nat.mul_add _ _ _]; omega
      have h_3Rt2 : 3 * R * (t * t) < 3 * (R * R) * (delta + 2) :=
        calc 3 * R * (t * t) ≤ 3 * R * (t * t) + t * t * t := Nat.le_add_right _ _
          _ < 3 * (R * R) * delta + 3 * (R * R) + 2 ^ 172 := hcube_lower
          _ ≤ 3 * (R * R) * (delta + 2) := h_rhs
      have h_assoc : 3 * (R * R) * (delta + 2) = 3 * R * (R * (delta + 2)) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [h_assoc] at h_3Rt2
      exact Nat.lt_of_mul_lt_mul_left h_3Rt2
    -- R·delta ≥ t² - 2R (in Nat; t² ≥ 6R > 2R so no underflow concern)
    have h_Rdelta_lb : t * t - 2 * R ≤ R * delta := by
      rw [show R * (delta + 2) = R * delta + R * 2 from Nat.mul_add _ _ _] at h_Rdelta2; omega
    -- 6·R·delta ≥ t²: from 5t² ≥ 12R (via t² ≥ 6R) and R·delta ≥ t² - 2R
    have h_6Rd : t * t ≤ 6 * (R * delta) := by
      have h5t2 : 12 * R ≤ 5 * (t * t) :=
        calc 12 * R ≤ 2 * (6 * R) := by omega
          _ ≤ 2 * (t * t) := Nat.mul_le_mul_left _ ht_sq_ge
          _ ≤ 5 * (t * t) := Nat.mul_le_mul_right _ (by omega)
      calc t * t ≤ 6 * (t * t) - 12 * R := by omega
        _ ≤ 6 * (t * t - 2 * R) := by omega
        _ ≤ 6 * (R * delta) := Nat.mul_le_mul_left _ h_Rdelta_lb
    -- t³ ≤ 6Rt·delta (multiply h_6Rd by t)
    have h_t3_le : t * t * t ≤ 6 * R * delta * t := by
      rw [show t * t * t = t * (t * t) from Nat.mul_assoc _ _ _,
          show 6 * R * delta * t = t * (6 * (R * delta)) from by
            simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]]
      exact Nat.mul_le_mul_left _ h_6Rd
    -- Main: 3R²·delta ≤ 3R·(t+delta)², then cancel 3R
    suffices h_3R : 3 * (R * R) * delta ≤ 3 * R * ((t + delta) * (t + delta)) by
      -- Rewrite to 3R * (R * delta) ≤ 3R * ((t+delta)²), then cancel 3R
      have h_assoc2 : 3 * (R * R) * delta = 3 * R * (R * delta) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [h_assoc2] at h_3R
      rw [show delta * R = R * delta from Nat.mul_comm _ _]
      exact Nat.le_of_mul_le_mul_left h_3R (by omega : 0 < 3 * R)
    -- 3R²·delta ≤ 3Rt² + t³ ≤ 3Rt² + 6Rt·delta ≤ 3R(t²+2t·delta+delta²) = 3R(t+delta)²
    have h_factor : 3 * R * (t * t) + 6 * R * delta * t + 3 * R * (delta * delta) =
        3 * R * (t * t + 2 * t * delta + delta * delta) := by
      -- 6·R·delta·t = 3·R·(2·t·delta) via associativity/commutativity
      have h6 : 6 * R * delta * t = 3 * R * (2 * t * delta) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [h6, ← Nat.mul_add, ← Nat.mul_add]
    calc 3 * (R * R) * delta
        ≤ 3 * R * (t * t) + t * t * t := hcube_upper
      _ ≤ 3 * R * (t * t) + 6 * R * delta * t := by omega
      _ ≤ 3 * R * (t * t) + 6 * R * delta * t + 3 * R * (delta * delta) := Nat.le_add_right _ _
      _ = 3 * R * (t * t + 2 * t * delta + delta * delta) := h_factor
      _ = 3 * R * ((t + delta) * (t + delta)) := by congr 1; exact (sq_sum_expand t delta).symm

-- Helper: given all the bounds, show the contradiction when x_norm = s³ and r_qc > s.
-- Factored out to avoid kernel deep recursion in the main theorem.
private theorem perfect_cube_no_overshoot (s R r_lo c : Nat)
    (hR_lo : 2 ^ 169 ≤ R) (hR_pos : 0 < R)
    (hc_def : c = r_lo * r_lo / R)
    (hc_strict : c < r_lo)
    (hrqc_eq : R + r_lo - c = s + 1)
    (hs_ge_R : R ≤ s)
    (hx_lb2 : R * R * R + 3 * (R * R) * r_lo ≤ s * s * s)
    (hx_ub : s * s * s < R * R * R + 3 * (R * R) * (r_lo + 1) + 2 ^ 172) :
    False := by
  have h_cube_expand := cube_sum_expand R (s - R)
  rw [Nat.add_sub_cancel' hs_ge_R] at h_cube_expand
  have hsR_eq : s - R = r_lo - c - 1 := by
    have : R + (r_lo - c) = s + 1 := by omega
    omega
  have hdelta_eq : r_lo - (s - R) = c + 1 := by
    rw [hsR_eq]
    omega
  have hdelta_pos : 0 < r_lo - (s - R) := hdelta_eq ▸ Nat.succ_pos _
  -- hcube_upper: from hx_lb2 and cube expansion
  have hcube_upper : 3 * (R * R) * (r_lo - (s - R)) ≤
      3 * R * ((s - R) * (s - R)) + (s - R) * (s - R) * (s - R) := by
    have h_from_lb : R * R * R + 3 * (R * R) * r_lo ≤
        R * R * R + 3 * (R * R) * (s - R) + 3 * R * ((s - R) * (s - R)) +
        (s - R) * (s - R) * (s - R) := by
      calc R * R * R + 3 * (R * R) * r_lo ≤ s * s * s := hx_lb2
        _ = _ := h_cube_expand
    have h_split : 3 * (R * R) * r_lo =
        3 * (R * R) * (s - R) + 3 * (R * R) * (r_lo - (s - R)) := by
      rw [← Nat.mul_add]; congr 1; omega
    omega
  -- hcube_lower: from hx_ub and cube expansion
  have hcube_lower : 3 * R * ((s - R) * (s - R)) + (s - R) * (s - R) * (s - R) <
      3 * (R * R) * (r_lo - (s - R)) + 3 * (R * R) + 2 ^ 172 := by
    have h_from_ub : R * R * R + 3 * (R * R) * (s - R) +
        3 * R * ((s - R) * (s - R)) + (s - R) * (s - R) * (s - R) <
        R * R * R + 3 * (R * R) * (r_lo + 1) + 2 ^ 172 := by
      calc R * R * R + 3 * (R * R) * (s - R) +
            3 * R * ((s - R) * (s - R)) + (s - R) * (s - R) * (s - R)
          = s * s * s := h_cube_expand.symm
        _ < R * R * R + 3 * (R * R) * (r_lo + 1) + 2 ^ 172 := hx_ub
    have h_rlo_split : 3 * (R * R) * (r_lo + 1) =
        3 * (R * R) * (s - R) + 3 * (R * R) * (r_lo - (s - R)) + 3 * (R * R) := by
      have : r_lo + 1 = (s - R) + (r_lo - (s - R)) + 1 := by omega
      rw [this, show (s - R) + (r_lo - (s - R)) + 1 =
        (s - R) + ((r_lo - (s - R)) + 1) from by omega]
      simp only [Nat.mul_add, Nat.mul_one, Nat.add_assoc]
    rw [h_rlo_split] at h_from_ub
    omega
  have h_qc := quad_correction_ge_delta R (s - R) (r_lo - (s - R))
    hR_lo hdelta_pos hcube_upper hcube_lower
  rw [show s - R + (r_lo - (s - R)) = r_lo from by omega] at h_qc
  have hc_ge_delta : r_lo - (s - R) ≤ c :=
    hc_def ▸ (Nat.le_div_iff_mul_le hR_pos).mpr h_qc
  -- delta = c + 1 ≤ c: contradiction
  omega

set_option exponentiation.threshold 1024 in
theorem r_qc_no_overshoot_on_cubes (x_hi_1 x_lo_1 : Nat)
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
    r_qc * r_qc * r_qc > x_norm →
      icbrt x_norm * icbrt x_norm * icbrt x_norm < x_norm := by
  simp only
  -- ======== Step 1: Extract base case properties via baseCase_bounds ========
  obtain ⟨hm_lo, _, _, _, hcube_le_w, hres_bound,
          hd_pos, _, hR_lo, _, hR_pos, hlimb_bound, hr_lo_bound⟩ :=
    baseCase_bounds x_hi_1 x_lo_1 hxhi_lo hxhi_hi hxlo
  -- Abbreviate
  let m := icbrt (x_hi_1 / 4)
  let w := x_hi_1 / 4
  let res := w - m * m * m
  let d := 3 * (m * m)
  let limb_hi := (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172
  let r_lo := (res * 2 ^ 86 + limb_hi) / d
  let R := m * 2 ^ 86
  let c := r_lo * r_lo / R
  let rem_kq := (res * 2 ^ 86 + limb_hi) % d
  let c_tail := x_lo_1 % 2 ^ 172
  have hrem_lt : rem_kq < d := Nat.mod_lt _ hd_pos
  have hctail_lt : c_tail < 2 ^ 172 := Nat.mod_lt _ (Nat.two_pow_pos 172)
  -- ======== Step 3: x_norm decomposition ========
  have hx_decomp := x_norm_decomp x_hi_1 x_lo_1 (m * m * m) hcube_le_w
  have hn_full := Nat.div_add_mod (res * 2 ^ 86 + limb_hi) d
  have h_num_eq : (res * 2 ^ 86 + limb_hi) = d * r_lo + rem_kq := hn_full.symm
  have h_num_mul : (d * r_lo + rem_kq) * 2 ^ 172 = d * r_lo * 2 ^ 172 + rem_kq * 2 ^ 172 :=
    Nat.add_mul _ _ _
  have hR3 := R_cube_factor m
  have hd_eq_3R2 := d_pow172_eq_3R_sq m
  have hrem_ub : rem_kq * 2 ^ 172 + c_tail < d * 2 ^ 172 + 2 ^ 172 := by
    have := Nat.mul_lt_mul_of_pos_right hrem_lt (Nat.two_pow_pos 172)
    omega
  -- x_norm ≥ R³ + 3R²·r_lo (lower bound, same as sub-lemma B)
  have hx_lb : m * m * m * 2 ^ 258 + d * r_lo * 2 ^ 172 ≤
      x_hi_1 * 2 ^ 256 + x_lo_1 := by
    rw [hx_decomp]
    rw [show ((x_hi_1 / 4 - m * m * m) * 2 ^ 86 +
        (x_hi_1 % 4 * 2 ^ 84 + x_lo_1 / 2 ^ 172)) = d * r_lo + rem_kq from h_num_eq]
    rw [h_num_mul]
    omega
  have hx_lb2 : R * R * R + 3 * (R * R) * r_lo ≤ x_hi_1 * 2 ^ 256 + x_lo_1 := by
    calc R * R * R + 3 * (R * R) * r_lo
        = m * m * m * 2 ^ 258 + 3 * (m * m) * r_lo * 2 ^ 172 := by
          rw [← hR3]
          show R * R * R + 3 * (R * R) * r_lo =
            R * R * R + 3 * (m * m) * r_lo * 2 ^ 172
          rw [← hd_eq_3R2]
          simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ = m * m * m * 2 ^ 258 + d * r_lo * 2 ^ 172 := by rfl
      _ ≤ x_hi_1 * 2 ^ 256 + x_lo_1 := hx_lb
  -- x_norm < R³ + 3R²·(r_lo + 1) + 2^172
  have hx_ub : x_hi_1 * 2 ^ 256 + x_lo_1 <
      R * R * R + 3 * (R * R) * (r_lo + 1) + 2 ^ 172 := by
    have hx_ub_raw : x_hi_1 * 2 ^ 256 + x_lo_1 <
        m * m * m * 2 ^ 258 + d * (r_lo + 1) * 2 ^ 172 + 2 ^ 172 := by
      rw [hx_decomp]
      rw [show ((x_hi_1 / 4 - m * m * m) * 2 ^ 86 +
          (x_hi_1 % 4 * 2 ^ 84 + x_lo_1 / 2 ^ 172)) = d * r_lo + rem_kq from h_num_eq]
      rw [h_num_mul]
      have : d * (r_lo + 1) * 2 ^ 172 = d * r_lo * 2 ^ 172 + d * 2 ^ 172 := by
        rw [show d * (r_lo + 1) = d * r_lo + d * 1 from Nat.mul_add _ _ _, Nat.mul_one,
            Nat.add_mul]
      exact by omega
    calc x_hi_1 * 2 ^ 256 + x_lo_1
        < m * m * m * 2 ^ 258 + d * (r_lo + 1) * 2 ^ 172 + 2 ^ 172 := hx_ub_raw
      _ = R * R * R + 3 * (R * R) * (r_lo + 1) + 2 ^ 172 := by
          have hdr1 : d * (r_lo + 1) * 2 ^ 172 = 3 * (R * R) * (r_lo + 1) := by
            show 3 * (m * m) * (r_lo + 1) * 2 ^ 172 = 3 * (R * R) * (r_lo + 1)
            rw [← hd_eq_3R2]
            simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
          rw [← hR3, hdr1]
  -- ======== Step 4: Main proof by contradiction ========
  intro h_over
  let s := icbrt (x_hi_1 * 2 ^ 256 + x_lo_1)
  have hcube_le := icbrt_cube_le (x_hi_1 * 2 ^ 256 + x_lo_1)
  have hsucc_gt := icbrt_lt_succ_cube (x_hi_1 * 2 ^ 256 + x_lo_1)
  by_cases h_not_perf : s * s * s < x_hi_1 * 2 ^ 256 + x_lo_1
  · exact h_not_perf
  · -- Perfect cube case: derive contradiction via perfect_cube_no_overshoot
    exfalso
    have h_perf : s * s * s = x_hi_1 * 2 ^ 256 + x_lo_1 :=
      Nat.le_antisymm hcube_le (Nat.not_lt.mp h_not_perf)
    have hB := r_qc_pred_cube_le x_hi_1 x_lo_1 hxhi_lo hxhi_hi hxlo
    simp only at hB
    have hrqc_gt_s : s < R + r_lo - c := by
      by_cases h : s < R + r_lo - c
      · exact h
      · exfalso; have h1 := cube_monotone (Nat.not_lt.mp h)
        rw [h_perf] at h1; exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h_over h1)
    have hrqc1_le_s : R + r_lo - c - 1 ≤ s := by
      -- If s < r_qc - 1, then (s+1)³ ≤ (r_qc-1)³ ≤ x_norm = s³,
      -- contradicting hsucc_gt: x_norm < (s+1)³.
      by_cases h_gt : s < R + r_lo - c - 1
      · exfalso
        have h1 := cube_monotone (show s + 1 ≤ R + r_lo - c - 1 from by omega)
        -- h1 and hB are both about the expanded form, so Nat.le_trans works
        have h2 := Nat.le_trans h1 hB
        -- h2 : (s+1)³ ≤ x_norm. But hsucc_gt : x_norm < (s+1)³.
        exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hsucc_gt h2)
      · exact Nat.not_lt.mp h_gt
    have hrqc_eq : R + r_lo - c = s + 1 := Nat.le_antisymm (by omega) (by omega)
    have hr_lo_pos : 0 < r_lo := by
      cases Nat.eq_or_lt_of_le (Nat.zero_le r_lo) with
      | inr h => exact h
      | inl h =>
        exfalso
        have hrl0 : r_lo = 0 := h.symm
        have hc0 : c = 0 := by
          rw [show c = r_lo * r_lo / R from rfl, hrl0]
          simp
        -- s + 1 = R, so hsucc_gt: x_norm < R³. But hx_lb2: R³ ≤ x_norm.
        rw [hrl0, hc0] at hrqc_eq
        have : R * R * R ≤ x_hi_1 * 2 ^ 256 + x_lo_1 := by
          calc R * R * R ≤ R * R * R + 3 * (R * R) * 0 := by omega
            _ = R * R * R + 3 * (R * R) * r_lo := by rw [hrl0]
            _ ≤ _ := hx_lb2
        rw [← h_perf] at this
        have : s + 1 = R := by omega
        have : x_hi_1 * 2 ^ 256 + x_lo_1 < (s + 1) * (s + 1) * (s + 1) := hsucc_gt
        rw [‹s + 1 = R›] at this
        omega
    have hR_gt_rlo : r_lo < R :=
      Nat.lt_of_lt_of_le hr_lo_bound (Nat.le_trans (Nat.pow_le_pow_right (by omega) (by omega : 87 ≤ 169)) hR_lo)
    have hc_strict : c < r_lo :=
      (Nat.div_lt_iff_lt_mul hR_pos).mpr
        (Nat.mul_lt_mul_of_pos_left hR_gt_rlo hr_lo_pos)
    have hs_ge_R : R ≤ s := by omega
    exact perfect_cube_no_overshoot s R r_lo c hR_lo hR_pos rfl hc_strict
      hrqc_eq hs_ge_R (h_perf ▸ hx_lb2) (h_perf ▸ hx_ub)


end Cbrt512Spec

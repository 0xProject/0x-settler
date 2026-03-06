/-
  Sub-lemma A: (r_qc + 2)³ > x_norm, giving icbrt ≤ r_qc + 1.
  Also: P2 c≤1 helper — (r_qc + 1)³ > x_norm when c ≤ 1.
-/
import Cbrt512Proof.GeneratedCbrt512Model
import Cbrt512Proof.CbrtBaseCase
import Cbrt512Proof.CbrtAlgebraic
import Cbrt512Proof.EvmBridge
import CbrtProof.CbrtCorrect

namespace Cbrt512Spec

open Cbrt512GeneratedModel

-- qc_undershoot_cube_lt is defined after sub-lemmas A, B, E1, E2 below.

-- ============================================================================
-- P2 helper (c ≤ 1): (r_qc + 1)³ > x_norm, hence icbrt ≤ r_qc
-- ============================================================================

set_option exponentiation.threshold 1024 in
/-- When c ≤ 1, the cube of (r_qc + 1) exceeds x_norm.
    Key: x_norm < R³ + 3R²·(r_lo+1) (tight upper bound from rem < 3m², c_tail < 2^172).
    And (r_qc+1)³ = (R+s)³ where s = r_lo-c+1, with 3Rs² + s³ ≥ 3R²c when c ≤ 1.
    For c=0: trivial (3Rs² ≥ 0 ≥ 0). For c=1: r_lo² ≥ R, so 3Rr_lo² ≥ 3R². -/
theorem r_qc_succ1_cube_gt_when_c_le1 (x_hi_1 x_lo_1 : Nat)
    (hxhi_lo : 2 ^ 253 ≤ x_hi_1) (hxhi_hi : x_hi_1 < WORD_MOD)
    (hxlo : x_lo_1 < WORD_MOD)
    (hc_le1 : let m := icbrt (x_hi_1 / 4)
              let d := 3 * (m * m)
              let res := x_hi_1 / 4 - m * m * m
              let limb_hi := (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172
              let r_lo := (res * 2 ^ 86 + limb_hi) / d
              r_lo * r_lo / (m * 2 ^ 86) ≤ 1) :
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
    x_norm < (r_qc + 1) * (r_qc + 1) * (r_qc + 1) := by
  simp only
  -- ======== Step 1: Base case properties ========
  have hbc := model_cbrtBaseCase_evm_correct x_hi_1 hxhi_lo hxhi_hi
  have hm_lo : 2 ^ 83 ≤ icbrt (x_hi_1 / 4) := hbc.2.2.2.1
  have hm_hi : icbrt (x_hi_1 / 4) < 2 ^ 85 := hbc.2.2.2.2.1
  have hcube_le_w : icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)
      ≤ x_hi_1 / 4 := hbc.2.2.2.2.2.1
  have hres_bound : x_hi_1 / 4 - icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)
      ≤ 3 * (icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)) + 3 * icbrt (x_hi_1 / 4) :=
    hbc.2.2.2.2.2.2.1
  have hd_pos : 3 * (icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)) > 0 :=
    hbc.2.2.2.2.2.2.2.2.2.2
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
  -- ======== Step 2: Key bounds ========
  have hR_lo : 2 ^ 169 ≤ R :=
    calc 2 ^ 169 = 2 ^ 83 * 2 ^ 86 := by rw [← Nat.pow_add]
      _ ≤ m * 2 ^ 86 := Nat.mul_le_mul_right _ hm_lo
  have hR_pos : 0 < R := by omega
  have hlimb_bound : limb_hi < 2 ^ 86 := by
    show (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172 < 2 ^ 86
    have hmod4 : x_hi_1 % 4 < 4 := Nat.mod_lt _ (by omega)
    have hdiv : x_lo_1 / 2 ^ 172 < 2 ^ 84 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 172)]
      calc x_lo_1 < WORD_MOD := hxlo
        _ = 2 ^ 84 * 2 ^ 172 := by unfold WORD_MOD; rw [← Nat.pow_add]
    have : (x_hi_1 % 4) * 2 ^ 84 < 2 ^ 86 :=
      calc (x_hi_1 % 4) * 2 ^ 84 < 4 * 2 ^ 84 :=
              Nat.mul_lt_mul_of_pos_right hmod4 (Nat.two_pow_pos 84)
        _ = 2 ^ 86 := by rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add]
    omega
  have hr_lo_bound : r_lo < 2 ^ 87 := by
    show (res * 2 ^ 86 + limb_hi) / d < 2 ^ 87
    rw [Nat.div_lt_iff_lt_mul hd_pos]
    have h2m : 2 * m ≤ m * m := Nat.mul_le_mul_right m (by omega)
    calc res * 2 ^ 86 + limb_hi
        < (res + 1) * 2 ^ 86 := by omega
      _ ≤ (3 * (m * m) + 3 * m + 1) * 2 ^ 86 := by
          apply Nat.mul_le_mul_right; exact Nat.succ_le_succ hres_bound
      _ ≤ (2 * (3 * (m * m))) * 2 ^ 86 := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ 87 * (3 * (m * m)) := by
          rw [show (2 : Nat) ^ 87 = 2 * 2 ^ 86 from by
            rw [show (87 : Nat) = 1 + 86 from rfl, Nat.pow_add]]; omega
  -- c ≤ r_lo
  have hc_le : c ≤ r_lo := by
    show r_lo * r_lo / R ≤ r_lo
    cases Nat.eq_or_lt_of_le (Nat.zero_le r_lo) with
    | inl h => rw [← h]; simp
    | inr h =>
      exact Nat.le_of_lt ((Nat.div_lt_iff_lt_mul hR_pos).mpr
        (Nat.mul_lt_mul_of_pos_left (by omega : r_lo < R) h))
  -- rem_kq < d
  have hrem_lt : rem_kq < d := Nat.mod_lt _ hd_pos
  -- c_tail < 2^172
  have hctail_lt : c_tail < 2 ^ 172 := Nat.mod_lt _ (Nat.two_pow_pos 172)
  -- ======== Step 3: Tight x_norm upper bound ========
  -- x_norm = m³·2^258 + (d·r_lo + rem)·2^172 + c_tail
  -- Since rem < d and c_tail < 2^172:
  --   (d·r_lo + rem)·2^172 + c_tail < (d·r_lo + d)·2^172 = d·(r_lo+1)·2^172
  -- So x_norm < m³·2^258 + d·(r_lo+1)·2^172 = R³ + 3R²·(r_lo+1)
  have hx_decomp := x_norm_decomp x_hi_1 x_lo_1 (m * m * m) hcube_le_w
  have hn_full := Nat.div_add_mod (res * 2 ^ 86 + limb_hi) d
  have hx_ub_tight : x_hi_1 * 2 ^ 256 + x_lo_1 <
      m * m * m * 2 ^ 258 + d * (r_lo + 1) * 2 ^ 172 := by
    rw [hx_decomp]
    have : (res * 2 ^ 86 + limb_hi) = d * r_lo + rem_kq := hn_full.symm
    rw [show ((x_hi_1 / 4 - m * m * m) * 2 ^ 86 +
        (x_hi_1 % 4 * 2 ^ 84 + x_lo_1 / 2 ^ 172)) = d * r_lo + rem_kq from this]
    have : (d * r_lo + rem_kq) * 2 ^ 172 = d * r_lo * 2 ^ 172 + rem_kq * 2 ^ 172 :=
      Nat.add_mul _ _ _
    have : d * (r_lo + 1) * 2 ^ 172 = d * r_lo * 2 ^ 172 + d * 2 ^ 172 := by
      rw [show d * (r_lo + 1) = d * r_lo + d * 1 from Nat.mul_add d r_lo 1, Nat.mul_one,
          Nat.add_mul]
    -- rem < d and c_tail < 2^172, so rem·2^172 + c_tail < d·2^172
    have : rem_kq * 2 ^ 172 + c_tail < d * 2 ^ 172 := by
      have := Nat.mul_lt_mul_of_pos_right hrem_lt (Nat.two_pow_pos 172)
      omega
    omega
  -- Rewrite d·(r_lo+1)·2^172 = 3R²·(r_lo+1)
  have hd_eq_3R2 := d_pow172_eq_3R_sq m
  have hR3 := R_cube_factor m
  have hx_ub_R : x_hi_1 * 2 ^ 256 + x_lo_1 <
      R * R * R + 3 * (R * R) * (r_lo + 1) := by
    have hd_rlo1 : d * (r_lo + 1) * 2 ^ 172 = 3 * (R * R) * (r_lo + 1) := by
      show 3 * (m * m) * (r_lo + 1) * 2 ^ 172 = 3 * (m * 2 ^ 86 * (m * 2 ^ 86)) * (r_lo + 1)
      rw [← hd_eq_3R2]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    calc x_hi_1 * 2 ^ 256 + x_lo_1
        < m * m * m * 2 ^ 258 + d * (r_lo + 1) * 2 ^ 172 := hx_ub_tight
      _ = R * R * R + 3 * (R * R) * (r_lo + 1) := by rw [hR3, hd_rlo1]
  -- ======== Step 4: (r_qc + 1)³ ≥ R³ + 3R²·(r_lo+1) when c ≤ 1 ========
  -- r_qc + 1 = R + r_lo - c + 1 = R + s where s = r_lo - c + 1
  have hrqc1_eq : m * 2 ^ 86 + r_lo - r_lo * r_lo / (m * 2 ^ 86) + 1 = R + (r_lo - c + 1) := by
    show R + r_lo - c + 1 = R + (r_lo - c + 1)
    omega
  rw [hrqc1_eq, cube_sum_expand R (r_lo - c + 1)]
  -- Goal: x_norm < R³ + 3R²·s + 3R·s² + s³ where s = r_lo - c + 1
  -- From hx_ub_R: x_norm < R³ + 3R²·(r_lo + 1)
  -- Suffices: R³ + 3R²·(r_lo+1) ≤ R³ + 3R²·s + 3R·s² + s³
  -- i.e., 3R²·(r_lo+1) ≤ 3R²·s + 3R·s² + s³
  -- s = r_lo - c + 1, so r_lo + 1 = s + c. Thus 3R²(r_lo+1) = 3R²(s+c) = 3R²s + 3R²c.
  -- Need: 3R²c ≤ 3R·s² + s³
  suffices h_suff : R * R * R + 3 * (R * R) * (r_lo + 1) ≤
      R * R * R + 3 * (R * R) * (r_lo - c + 1) +
      3 * R * ((r_lo - c + 1) * (r_lo - c + 1)) +
      (r_lo - c + 1) * (r_lo - c + 1) * (r_lo - c + 1) from
    Nat.lt_of_lt_of_le hx_ub_R h_suff
  -- Split: 3R²(r_lo+1) = 3R²·s + 3R²·c
  have hsc : r_lo - c + 1 + c = r_lo + 1 := by omega
  have h_split : 3 * (R * R) * (r_lo + 1) =
      3 * (R * R) * (r_lo - c + 1) + 3 * (R * R) * c := by
    rw [← Nat.mul_add]; congr 1; exact hsc.symm
  rw [h_split]
  -- Need: 3R²c ≤ 3Rs² + s³
  -- Case split on c
  by_cases hc0 : c = 0
  · -- c = 0: LHS has 3R²·0 = 0 extra, RHS has 3Rs² + s³ ≥ 0 extra. Trivially holds.
    rw [hc0, Nat.mul_zero]; omega
  · -- c = 1 (since c ≤ 1 and c ≠ 0)
    have hc1 : c = 1 := Nat.le_antisymm hc_le1 (Nat.one_le_iff_ne_zero.mpr hc0)
    -- s = r_lo - c + 1 = r_lo (since c = 1)
    have hs_eq : r_lo - c + 1 = r_lo := by omega
    -- Need: 3R²c ≤ 3Rs² + s³, i.e., 3R² ≤ 3R·r_lo² + r_lo³
    -- From c = 1: r_lo² / R ≥ 1, so r_lo² ≥ R.
    have hrlo_sq_ge_R : R ≤ r_lo * r_lo := by
      show m * 2 ^ 86 ≤ r_lo * r_lo
      have hc_ge1 : 1 ≤ r_lo * r_lo / (m * 2 ^ 86) := by
        show 1 ≤ c; omega
      -- 1 ≤ r_lo²/R means R * 1 ≤ r_lo² (from div_mul_le + 1 ≤ quotient)
      calc m * 2 ^ 86
          = (m * 2 ^ 86) * 1 := (Nat.mul_one _).symm
        _ ≤ (m * 2 ^ 86) * (r_lo * r_lo / (m * 2 ^ 86)) := Nat.mul_le_mul_left _ hc_ge1
        _ = r_lo * r_lo / (m * 2 ^ 86) * (m * 2 ^ 86) := Nat.mul_comm _ _
        _ ≤ r_lo * r_lo := Nat.div_mul_le_self _ _
    -- 3R·r_lo² ≥ 3R·R = 3R², so 3R·s² + s³ ≥ 3R² = 3R²·c
    -- Rewrite s = r_lo first (before c = 1 substitution)
    rw [hs_eq]
    rw [hc1, Nat.mul_one]
    -- Goal: R³ + (3R²·r_lo + 3R²) ≤ R³ + 3R²·r_lo + 3R·(r_lo²) + r_lo³
    -- Suffices: 3R² ≤ 3R·(r_lo²) + r_lo³
    -- From 3R·(r_lo²) ≥ 3R·R = 3R²
    have h3RR : 3 * (R * R) = 3 * R * R := by
      simp only [Nat.mul_assoc]
    rw [h3RR]
    have : 3 * R * R ≤ 3 * R * (r_lo * r_lo) := Nat.mul_le_mul_left _ hrlo_sq_ge_R
    omega

-- ============================================================================
-- Sub-lemma A: Lower bound — (r_qc + 1)³ > x_norm
-- ============================================================================

set_option exponentiation.threshold 1024 in
/-- The cube of (r_qc + 2) exceeds x_norm.
    Combined with icbrt_cube_le, this gives icbrt(x_norm) ≤ r_qc + 1.
    Note: the stronger bound icbrt ≤ r_qc does NOT hold for the base r_qc
    when c ≥ 2 (the quadratic correction can over-subtract). The undershoot
    correction in the QC recovers the tighter bound for the actual output.

    Proof: x_norm = R³ + 3R²·r_lo + rem·2^172 + c_tail < R³ + 3R²(r_lo+1) + 2^172.
    (r_qc+2)³ = (R+s')³ where s' = r_lo - c + 2.
    We show 3R²(1-c) + 3R·s'² + s'³ > 2^172, using:
    - For c ≤ 1: 3R²(1-c) ≥ 0 and 12R > 2^172.
    - For c ≥ 2: s'² > R(c-1) since 2(c-2)r_lo < R, giving 3R(s'²-R(c-1)) >> 2^172. -/
theorem r_qc_succ2_cube_gt (x_hi_1 x_lo_1 : Nat)
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
    x_norm < (r_qc + 2) * (r_qc + 2) * (r_qc + 2) := by
  simp only
  -- ======== Step 1: Extract base case properties ========
  have hbc := model_cbrtBaseCase_evm_correct x_hi_1 hxhi_lo hxhi_hi
  have hm_lo : 2 ^ 83 ≤ icbrt (x_hi_1 / 4) := hbc.2.2.2.1
  have hm_hi : icbrt (x_hi_1 / 4) < 2 ^ 85 := hbc.2.2.2.2.1
  have hcube_le_w : icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)
      ≤ x_hi_1 / 4 := hbc.2.2.2.2.2.1
  have hres_bound : x_hi_1 / 4 - icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)
      ≤ 3 * (icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)) + 3 * icbrt (x_hi_1 / 4) :=
    hbc.2.2.2.2.2.2.1
  have hd_pos : 3 * (icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)) > 0 :=
    hbc.2.2.2.2.2.2.2.2.2.2
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
  -- ======== Step 2: Key bounds ========
  -- R bounds
  have hR_lo : 2 ^ 169 ≤ R :=
    calc 2 ^ 169 = 2 ^ 83 * 2 ^ 86 := by rw [← Nat.pow_add]
      _ ≤ m * 2 ^ 86 := Nat.mul_le_mul_right _ hm_lo
  have hR_lt : R < 2 ^ 171 :=
    calc m * 2 ^ 86
        < 2 ^ 85 * 2 ^ 86 := Nat.mul_lt_mul_of_pos_right hm_hi (Nat.two_pow_pos 86)
      _ = 2 ^ 171 := by rw [← Nat.pow_add]
  have hR_pos : 0 < R := by omega
  -- r_lo < 2^87 (reuse from r_qc_lt_pow172's proof pattern)
  have hlimb_bound : limb_hi < 2 ^ 86 := by
    show (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172 < 2 ^ 86
    have hmod4 : x_hi_1 % 4 < 4 := Nat.mod_lt _ (by omega)
    have hdiv : x_lo_1 / 2 ^ 172 < 2 ^ 84 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 172)]
      calc x_lo_1 < WORD_MOD := hxlo
        _ = 2 ^ 84 * 2 ^ 172 := by unfold WORD_MOD; rw [← Nat.pow_add]
    have : (x_hi_1 % 4) * 2 ^ 84 < 2 ^ 86 :=
      calc (x_hi_1 % 4) * 2 ^ 84 < 4 * 2 ^ 84 :=
              Nat.mul_lt_mul_of_pos_right hmod4 (Nat.two_pow_pos 84)
        _ = 2 ^ 86 := by rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add]
    omega
  have hr_lo_bound : r_lo < 2 ^ 87 := by
    show (res * 2 ^ 86 + limb_hi) / d < 2 ^ 87
    rw [Nat.div_lt_iff_lt_mul hd_pos]
    have h2m : 2 * m ≤ m * m := Nat.mul_le_mul_right m (by omega)
    calc res * 2 ^ 86 + limb_hi
        < (res + 1) * 2 ^ 86 := by omega
      _ ≤ (3 * (m * m) + 3 * m + 1) * 2 ^ 86 := by
          apply Nat.mul_le_mul_right; exact Nat.succ_le_succ hres_bound
      _ ≤ (2 * (3 * (m * m))) * 2 ^ 86 := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ 87 * (3 * (m * m)) := by
          rw [show (2 : Nat) ^ 87 = 2 * 2 ^ 86 from by
            rw [show (87 : Nat) = 1 + 86 from rfl, Nat.pow_add]]; omega
  -- c ≤ r_lo (since r_lo < R)
  have hc_le : c ≤ r_lo := by
    show r_lo * r_lo / R ≤ r_lo
    cases Nat.eq_or_lt_of_le (Nat.zero_le r_lo) with
    | inl h => rw [← h]; simp
    | inr h =>
      exact Nat.le_of_lt ((Nat.div_lt_iff_lt_mul hR_pos).mpr
        (Nat.mul_lt_mul_of_pos_left (by omega : r_lo < R) h))
  -- rem_kq < d
  have hrem_lt : rem_kq < d := Nat.mod_lt _ hd_pos
  -- c_tail < 2^172
  have hctail_lt : c_tail < 2 ^ 172 := Nat.mod_lt _ (Nat.two_pow_pos 172)
  -- ======== Step 3: x_norm upper bound ========
  -- x_norm = m³·2^258 + n_full·2^172 + c_tail (from x_norm_decomp)
  -- where n_full = d·r_lo + rem_kq. Since rem_kq < d and c_tail < 2^172:
  -- x_norm = R³ + (d·r_lo + rem_kq)·2^172 + c_tail < R³ + d·(r_lo+1)·2^172 + 2^172
  have hx_decomp := x_norm_decomp x_hi_1 x_lo_1 (m * m * m) hcube_le_w
  have hn_full := Nat.div_add_mod (res * 2 ^ 86 + limb_hi) d
  -- hn_full : d * r_lo + rem_kq = n_full
  have hrem_ub : rem_kq * 2 ^ 172 + c_tail < d * 2 ^ 172 + 2 ^ 172 := by
    have := Nat.mul_lt_mul_of_pos_right hrem_lt (Nat.two_pow_pos 172)
    omega
  -- x_norm < m³·2^258 + d*(r_lo+1)*2^172 + 2^172
  have hx_ub : x_hi_1 * 2 ^ 256 + x_lo_1 <
      m * m * m * 2 ^ 258 + d * (r_lo + 1) * 2 ^ 172 + 2 ^ 172 := by
    rw [hx_decomp]
    -- LHS = m³·2^258 + n_full·2^172 + c_tail
    -- n_full = d·r_lo + rem_kq, so n_full·2^172 = d·r_lo·2^172 + rem_kq·2^172
    -- Need: d·r_lo·2^172 + rem_kq·2^172 + c_tail < d·(r_lo+1)·2^172 + 2^172
    -- = d·r_lo·2^172 + d·2^172 + 2^172
    -- i.e., rem_kq·2^172 + c_tail < d·2^172 + 2^172 ✓ (from hrem_ub)
    have : (res * 2 ^ 86 + limb_hi) = d * r_lo + rem_kq := hn_full.symm
    -- n_full * 2^172 = (d * r_lo + rem_kq) * 2^172
    rw [show ((x_hi_1 / 4 - m * m * m) * 2 ^ 86 +
        (x_hi_1 % 4 * 2 ^ 84 + x_lo_1 / 2 ^ 172)) = d * r_lo + rem_kq from this]
    -- Goal: m³·2^258 + (d·r_lo + rem_kq)·2^172 + c_tail < m³·2^258 + d·(r_lo+1)·2^172 + 2^172
    have : (d * r_lo + rem_kq) * 2 ^ 172 = d * r_lo * 2 ^ 172 + rem_kq * 2 ^ 172 :=
      Nat.add_mul _ _ _
    have : d * (r_lo + 1) * 2 ^ 172 = d * r_lo * 2 ^ 172 + d * 2 ^ 172 := by
      rw [show d * (r_lo + 1) = d * r_lo + d * 1 from Nat.mul_add d r_lo 1, Nat.mul_one,
          Nat.add_mul]
    omega
  -- ======== Step 4: (R + s')³ > R³ + d·(r_lo+1)·2^172 + 2^172 ========
  -- Using R³ = m³·2^258, d·2^172 = 3R², this is:
  -- (R + s')³ > R³ + 3R²·(r_lo+1) + 2^172
  -- Expand: 3R²·s' + 3R·s'² + s'³ > 3R²·(r_lo+1) + 2^172
  -- i.e., 3R²·(s' - r_lo - 1) + 3R·s'² + s'³ > 2^172
  -- i.e., 3R²·(1 - c) + 3R·s'² + s'³ > 2^172  (in Int)
  -- But we need to connect d·(r_lo+1)·2^172 to 3R²·(r_lo+1):
  have hd_eq_3R2 := d_pow172_eq_3R_sq m
  -- d·2^172 = 3R² (definitionally via hd_eq_3R2)
  -- So d·(r_lo+1)·2^172 = 3R²·(r_lo+1)
  -- Goal: (R + s')³ > m³·2^258 + d·(r_lo+1)·2^172 + 2^172
  -- = R³ + 3R²·(r_lo+1) + 2^172  (using R³ = m³·2^258 and d·2^172 = 3R²)
  -- Key: r_qc + 2 = R + r_lo - c + 2 = R + s'  (Nat subtraction is fine since c ≤ r_lo)
  have hrqc2_eq : m * 2 ^ 86 + r_lo - r_lo * r_lo / (m * 2 ^ 86) + 2 = R + (r_lo - c + 2) := by
    show R + r_lo - c + 2 = R + (r_lo - c + 2)
    omega
  rw [hrqc2_eq]
  -- Expand cube
  rw [cube_sum_expand R (r_lo - c + 2)]
  -- RHS = R³ + 3R²·s' + 3R·s'² + s'³
  -- Need: R³ + 3R²·(r_lo+1) + 2^172 + ... < R³ + 3R²·s' + 3R·s'² + s'³
  -- But we're comparing x_norm (via hx_ub) to the expanded cube.
  -- Combine hx_ub with the goal.
  -- Goal is now: x_hi_1 * 2^256 + x_lo_1 < R³ + 3R²·s' + 3R·s'² + s'³
  -- From hx_ub: x_hi_1 * 2^256 + x_lo_1 < m³·2^258 + d·(r_lo+1)·2^172 + 2^172
  -- Suffices: m³·2^258 + d·(r_lo+1)·2^172 + 2^172 ≤ R³ + 3R²·s' + 3R·s'² + s'³
  -- i.e., R³ + 3R²·(r_lo+1) + 2^172 ≤ R³ + 3R²·s' + 3R·s'² + s'³
  -- i.e., 3R²·(r_lo+1) + 2^172 ≤ 3R²·s' + 3R·s'² + s'³
  -- Since s' = r_lo - c + 2 ≥ r_lo + 1 when c ≤ 1, and for c ≥ 2 the s'² term dominates
  -- Rewrite RHS using hR3 and hd_eq_3R2
  have hR3 := R_cube_factor m
  -- R³ = m³ · 2^258
  -- d·(r_lo+1)·2^172 = d·2^172·(r_lo+1) = 3R²·(r_lo+1)
  -- 3R² = 3·(R·R) = 3·(m·2^86)·(m·2^86)
  -- Need to show: m³·2^258 + d·(r_lo+1)·2^172 + 2^172 ≤ R·R·R + 3·(R·R)·s' + 3·R·(s'·s') + s'·s'·s'
  -- Rewrite R·R·R = m³·2^258
  -- And 3·(R·R)·(r_lo+1) = d·(r_lo+1)·2^172 (from hd_eq_3R2)
  -- Hmm, this requires careful Nat equalities. Let me use calc.
  suffices h_suff : m * m * m * 2 ^ 258 + d * (r_lo + 1) * 2 ^ 172 + 2 ^ 172 ≤
      R * R * R + 3 * (R * R) * (r_lo - c + 2) + 3 * R * ((r_lo - c + 2) * (r_lo - c + 2)) +
      (r_lo - c + 2) * (r_lo - c + 2) * (r_lo - c + 2) from
    Nat.lt_of_lt_of_le hx_ub h_suff
  -- s' ≥ 2 (needed inside the suffices proof)
  have hs'_ge_2 : 2 ≤ r_lo - c + 2 := by omega
  -- Rewrite m³·2^258 = R³
  rw [← hR3]
  -- Rewrite d·(r_lo+1)·2^172: d·2^172 = 3·(R·R), so d·(r_lo+1)·2^172 = 3·(R·R)·(r_lo+1)
  -- d·(r_lo+1)·2^172 = d·2^172·(r_lo+1) (associativity)
  have hd_rlo1 : d * (r_lo + 1) * 2 ^ 172 = 3 * (R * R) * (r_lo + 1) := by
    show 3 * (m * m) * (r_lo + 1) * 2 ^ 172 = 3 * (m * 2 ^ 86 * (m * 2 ^ 86)) * (r_lo + 1)
    rw [← hd_eq_3R2]
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [hd_rlo1]
  -- Goal: R³ + 3R²·(r_lo+1) + 2^172 ≤ R³ + 3R²·s' + 3R·s'² + s'³
  -- Cancel R³
  -- Need: 3R²·(r_lo+1) + 2^172 ≤ 3R²·s' + 3R·s'² + s'³
  -- Case split on c
  by_cases hc_le1 : c ≤ 1
  · -- Case c ≤ 1: s' = r_lo - c + 2 ≥ r_lo + 1
    have hs'_ge_rlo1 : r_lo + 1 ≤ r_lo - c + 2 := by omega
    -- 3R²·(r_lo+1) ≤ 3R²·s'
    have h1 : 3 * (R * R) * (r_lo + 1) ≤ 3 * (R * R) * (r_lo - c + 2) :=
      Nat.mul_le_mul_left _ hs'_ge_rlo1
    -- 3R·s'² ≥ 3R·4 = 12R > 2^172
    have h_s'sq : 4 ≤ (r_lo - c + 2) * (r_lo - c + 2) := Nat.mul_le_mul hs'_ge_2 hs'_ge_2
    have h_12R : 2 ^ 172 ≤ 12 * R := by
      calc 2 ^ 172 = 2 * 2 ^ 171 := by rw [show (172 : Nat) = 1 + 171 from rfl, Nat.pow_add]
        _ ≤ 2 * (6 * R) := Nat.mul_le_mul_left _ (by omega)
        _ = 12 * R := by omega
    have h_3Rs'2 : 2 ^ 172 ≤ 3 * R * ((r_lo - c + 2) * (r_lo - c + 2)) :=
      calc 2 ^ 172 ≤ 12 * R := h_12R
        _ = 3 * R * 4 := by omega
        _ ≤ 3 * R * ((r_lo - c + 2) * (r_lo - c + 2)) := Nat.mul_le_mul_left _ h_s'sq
    -- Chain: R³ + 3R²(r_lo+1) + 2^172 ≤ R³ + 3R²s' + 3Rs'² ≤ R³ + 3R²s' + 3Rs'² + s'³
    have step1 : R * R * R + 3 * (R * R) * (r_lo + 1) + 2 ^ 172 ≤
        R * R * R + 3 * (R * R) * (r_lo - c + 2) + 3 * R * ((r_lo - c + 2) * (r_lo - c + 2)) :=
      Nat.add_le_add (Nat.add_le_add (Nat.le_refl _) h1) h_3Rs'2
    exact Nat.le_trans step1 (Nat.le_add_right _ _)
  · -- Case c ≥ 2: s'² > R(c-1) since 2cr_lo < R
    have hc_ge2 : 2 ≤ c := by omega
    have hcR_le : c * R ≤ r_lo * r_lo := Nat.div_mul_le_self _ _
    -- Bound c*r_lo: from c*R ≤ r_lo², c*r_lo*R ≤ r_lo³ < 2^261, so c*r_lo < 2^92
    -- c*r_lo ≤ r_lo²/R * r_lo ≤ r_lo³/R < 2^261/2^169 = 2^92
    -- Direct approach: c ≤ r_lo (from hc_le), so c*r_lo ≤ r_lo².
    -- Also c*R ≤ r_lo², so c ≤ r_lo²/R < (2^87)²/2^169 = 2^174/2^169 = 2^5 = 32.
    have hc_lt_32 : c < 32 := by
      -- c*R ≤ r_lo² < (2^87)² = 2^174, and R ≥ 2^169
      have : c * R < 2 ^ 174 := Nat.lt_of_le_of_lt hcR_le
        (calc r_lo * r_lo
            ≤ r_lo * 2 ^ 87 := Nat.mul_le_mul_left _ (Nat.le_of_lt hr_lo_bound)
          _ < 2 ^ 87 * 2 ^ 87 := Nat.mul_lt_mul_of_pos_right hr_lo_bound (Nat.two_pow_pos 87)
          _ = 2 ^ 174 := by rw [← Nat.pow_add])
      -- c < 2^174 / R ≤ 2^174 / 2^169 = 2^5 = 32
      have h174 : (2 : Nat) ^ 174 = 32 * 2 ^ 169 := by
        rw [show (174 : Nat) = 5 + 169 from rfl, Nat.pow_add]
      by_cases hc0 : c = 0; · omega
      · exact Nat.lt_of_mul_lt_mul_right
          (calc c * R < 2 ^ 174 := ‹_›
            _ = 32 * 2 ^ 169 := h174
            _ ≤ 32 * R := Nat.mul_le_mul_left _ hR_lo)
    -- c*r_lo < 32 * 2^87 = 2^92
    have hcr_lt : c * r_lo < 2 ^ 92 :=
      calc c * r_lo < 32 * r_lo := Nat.mul_lt_mul_of_pos_right hc_lt_32 (by omega)
        _ ≤ 32 * 2 ^ 87 := Nat.mul_le_mul_left _ (Nat.le_of_lt hr_lo_bound)
        _ = 2 ^ 92 := by rw [show (32 : Nat) = 2 ^ 5 from rfl, ← Nat.pow_add]
    -- 2*c*r_lo < R (since 2 * 2^92 = 2^93 ≤ 2^169 ≤ R)
    have h2cr : 2 * c * r_lo < R := by
      calc 2 * c * r_lo = 2 * (c * r_lo) := Nat.mul_assoc 2 c r_lo
        _ < 2 * 2 ^ 92 := Nat.mul_lt_mul_of_pos_left hcr_lt (by omega)
        _ = 2 ^ 93 := by rw [show (93 : Nat) = 1 + 92 from rfl, Nat.pow_add]
        _ ≤ R := Nat.le_trans (Nat.pow_le_pow_right (by omega) (by omega : 93 ≤ 169)) hR_lo
    -- Key algebraic identity: (r_lo-c)² + 2cr_lo = r_lo² + c²
    have hsq_id : (r_lo - c) * (r_lo - c) + 2 * c * r_lo = r_lo * r_lo + c * c := by
      suffices h : (↑((r_lo - c) * (r_lo - c) + 2 * c * r_lo) : Int) =
          ↑(r_lo * r_lo + c * c) by exact_mod_cast h
      push_cast
      have hsub : (↑(r_lo - c) : Int) = ↑r_lo - ↑c := by omega
      rw [hsub]
      simp only [show (2 : Int) = 1 + 1 from rfl,
                 Int.add_mul, Int.one_mul,
                 Int.sub_mul, Int.mul_sub]
      simp only [Int.mul_comm]; omega
    -- R(c-1) + R = Rc ≤ r_lo²
    have hRc1_R : R * (c - 1) + R ≤ r_lo * r_lo := by
      -- c ≥ 2, so c - 1 + 1 = c. Then R*(c-1) + R = R*((c-1)+1) = R*c ≤ r_lo²
      calc R * (c - 1) + R
          = R * (c - 1) + R * 1 := by rw [Nat.mul_one]
        _ = R * (c - 1 + 1) := (Nat.mul_add R (c - 1) 1).symm
        _ = R * c := by congr 1; omega
        _ = c * R := Nat.mul_comm R c
        _ ≤ r_lo * r_lo := hcR_le
    -- (r_lo-c)² ≥ R(c-1) + 1 (since (r_lo-c)² ≥ r_lo² - 2cr_lo ≥ R(c-1) + R - 2cr_lo > R(c-1))
    have hrlc_sq : R * (c - 1) + 1 ≤ (r_lo - c) * (r_lo - c) := by
      -- From hsq_id: (r_lo-c)² = r_lo² + c² - 2cr_lo ≥ r_lo² - 2cr_lo
      -- From hRc1_R: R(c-1) + R ≤ r_lo²
      -- From h2cr: 2cr_lo < R
      -- So (r_lo-c)² ≥ r_lo² - 2cr_lo ≥ (R(c-1) + R) - 2cr_lo > R(c-1)
      have : r_lo * r_lo ≤ (r_lo - c) * (r_lo - c) + 2 * c * r_lo := by
        rw [hsq_id]; omega
      omega
    -- (r_lo-c+2)² ≥ (r_lo-c)² + 4
    have hs'sq_ge : (r_lo - c) * (r_lo - c) + 4 ≤ (r_lo - c + 2) * (r_lo - c + 2) := by
      -- (a+2)² = a² + 4a + 4 ≥ a² + 4
      -- In Nat: (r_lo - c + 2)² ≥ (r_lo - c)² + 4 since r_lo - c ≥ 0
      have h : (r_lo - c + 2) * (r_lo - c + 2) =
          (r_lo - c) * (r_lo - c) + 4 * (r_lo - c) + 4 := by
        suffices hi : (↑((r_lo - c + 2) * (r_lo - c + 2)) : Int) =
            ↑((r_lo - c) * (r_lo - c) + 4 * (r_lo - c) + 4) by exact_mod_cast hi
        push_cast
        have hsub : (↑(r_lo - c) : Int) = ↑r_lo - ↑c := by omega
        rw [hsub]
        simp only [show (4 : Int) = 2 * 2 from rfl, show (2 : Int) = 1 + 1 from rfl,
                   Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one,
                   Int.sub_mul, Int.mul_sub]
        simp only [Int.mul_comm]; omega
      omega
    -- s'² ≥ R(c-1) + 5
    have hs'sq_bound : R * (c - 1) + 5 ≤ (r_lo - c + 2) * (r_lo - c + 2) := by omega
    -- 3R·s'² ≥ 3R·(R(c-1) + 5) = 3R²(c-1) + 15R
    have h_3R_mul : 3 * R * (R * (c - 1) + 5) ≤
        3 * R * ((r_lo - c + 2) * (r_lo - c + 2)) := Nat.mul_le_mul_left _ hs'sq_bound
    -- 15R ≥ 2^172
    have h15R : 2 ^ 172 ≤ 15 * R := by
      calc 2 ^ 172 = 8 * 2 ^ 169 := by
            rw [show (172 : Nat) = 3 + 169 from rfl, Nat.pow_add]
        _ ≤ 8 * R := Nat.mul_le_mul_left _ hR_lo
        _ ≤ 15 * R := Nat.mul_le_mul_right _ (by omega)
    -- Split 3R²(r_lo+1) = 3R²·s' + 3R²(c-1)
    have hrlo1_split : 3 * (R * R) * (r_lo + 1) =
        3 * (R * R) * (r_lo - c + 2) + 3 * (R * R) * (c - 1) := by
      rw [← Nat.mul_add]; congr 1; omega
    rw [hrlo1_split]
    -- Rewrite 3R²(c-1) = 3R·(R·(c-1))
    have hRR_assoc : 3 * (R * R) * (c - 1) = 3 * R * (R * (c - 1)) := by
      simp only [Nat.mul_assoc, Nat.mul_left_comm]
    rw [hRR_assoc]
    -- Goal: 3R²s' + 3R(R(c-1)) + 2^172 ≤ 3R²s' + 3Rs'² + s'³
    -- Need: 3R(R(c-1)) + 2^172 ≤ 3Rs'² + s'³
    -- From h_3R_mul: 3R(R(c-1)) + 15R ≤ 3Rs'²
    -- From h15R: 2^172 ≤ 15R
    -- So 3R(R(c-1)) + 2^172 ≤ 3R(R(c-1)) + 15R ≤ 3Rs'² ≤ 3Rs'² + s'³
    have step1 : 3 * R * (R * (c - 1)) + 2 ^ 172 ≤
        3 * R * (R * (c - 1)) + 15 * R := by omega
    have step2 : 3 * R * (R * (c - 1)) + 15 * R ≤
        3 * R * ((r_lo - c + 2) * (r_lo - c + 2)) := by
      -- 3R(R(c-1) + 5) ≤ 3Rs'² from h_3R_mul, and R(c-1) + 5 ≤ R(c-1) + 15R/3R...
      -- Actually: 3R·(R(c-1) + 5) = 3R·R(c-1) + 15R
      -- And h_3R_mul says 3R·(R(c-1) + 5) ≤ 3R·s'²
      calc 3 * R * (R * (c - 1)) + 15 * R
          = 3 * R * (R * (c - 1)) + 3 * R * 5 := by omega
        _ = 3 * R * (R * (c - 1) + 5) := (Nat.mul_add (3 * R) _ 5).symm
        _ ≤ 3 * R * ((r_lo - c + 2) * (r_lo - c + 2)) := h_3R_mul
    calc R * R * R + (3 * (R * R) * (r_lo - c + 2) + 3 * R * (R * (c - 1))) + 2 ^ 172
        ≤ R * R * R + (3 * (R * R) * (r_lo - c + 2) +
            3 * R * ((r_lo - c + 2) * (r_lo - c + 2))) := by
          have := Nat.le_trans step1 step2; omega
      _ ≤ R * R * R + 3 * (R * R) * (r_lo - c + 2) +
            3 * R * ((r_lo - c + 2) * (r_lo - c + 2)) +
            (r_lo - c + 2) * (r_lo - c + 2) * (r_lo - c + 2) := by omega


end Cbrt512Spec

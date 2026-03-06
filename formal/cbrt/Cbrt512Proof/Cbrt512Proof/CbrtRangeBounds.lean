/-
  Range bounds: R_MAX, r_qc ≤ R_MAX, R + r_lo ≤ R_MAX + 1.
  Sub-lemma E1: the cube bound r_qc³ < WORD_MOD².
-/
import Cbrt512Proof.GeneratedCbrt512Model
import Cbrt512Proof.CbrtNumericCerts
import Cbrt512Proof.CbrtBaseCase
import Cbrt512Proof.CbrtAlgebraic
import Cbrt512Proof.EvmBridge
import CbrtProof.CbrtCorrect

namespace Cbrt512Spec

open Cbrt512GeneratedModel

set_option exponentiation.threshold 1024 in
/-- For m ≥ 2^83, (3m+1) · 2^86 ≤ 27 · m · m.
    Proof: 27m² - 3m·2^86 = 3m(9m - 2^86) ≥ 3·2^83·2^83 = 3·2^166 ≥ 2^86. -/
private theorem tight_numerator_bound (m : Nat) (hm : 2 ^ 83 ≤ m) :
    (3 * m + 1) * 2 ^ 86 ≤ 27 * (m * m) := by
  -- 9m ≥ 9 · 2^83 = 2^86 + 2^83
  have h9m : 2 ^ 86 + 2 ^ 83 ≤ 9 * m := by omega
  -- So 9m - 2^86 ≥ 2^83
  have h9m_sub : 2 ^ 83 ≤ 9 * m - 2 ^ 86 := by omega
  -- 3m(9m - 2^86) ≥ 3 · 2^83 · 2^83 = 3 · 2^166
  have h_prod : 3 * 2 ^ 166 ≤ 3 * m * (9 * m - 2 ^ 86) :=
    calc 3 * 2 ^ 166
        = 3 * (2 ^ 83 * 2 ^ 83) := by rw [show (166 : Nat) = 83 + 83 from rfl, Nat.pow_add]
      _ ≤ 3 * (m * (9 * m - 2 ^ 86)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hm h9m_sub)
      _ = 3 * m * (9 * m - 2 ^ 86) := (Nat.mul_assoc 3 m _).symm
  -- 3 · 2^166 ≥ 2^86
  have h_big : (2 : Nat) ^ 86 ≤ 3 * 2 ^ 166 := by
    show 2 ^ 86 ≤ 3 * 2 ^ 166
    calc 2 ^ 86 ≤ 1 * 2 ^ 166 := by
          show 2 ^ 86 ≤ 2 ^ 166
          exact Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ 3 * 2 ^ 166 := Nat.mul_le_mul_right _ (by omega)
  -- Now: (3m+1) · 2^86 = 3m · 2^86 + 2^86 ≤ 3m · 2^86 + 3m(9m - 2^86)
  --   = 3m · (2^86 + 9m - 2^86) = 3m · 9m = 27m²
  -- But we need to handle Nat subtraction carefully.
  -- 27m² = 3m · 9m = 3m · (2^86 + (9m - 2^86))  [since 9m ≥ 2^86]
  --       = 3m · 2^86 + 3m · (9m - 2^86)
  -- 27m² = 3m · (2^86 + (9m - 2^86)) = 3m·2^86 + 3m·(9m-2^86)
  have h_split : 27 * (m * m) = 3 * m * 2 ^ 86 + 3 * m * (9 * m - 2 ^ 86) := by
    rw [← Nat.mul_add]
    -- 2^86 + (9m - 2^86) = 9m
    have h9m_eq : 2 ^ 86 + (9 * m - 2 ^ 86) = 9 * m := by omega
    rw [h9m_eq]
    -- 3m · 9m = 27 · (m·m)
    suffices h : (↑(27 * (m * m)) : Int) = ↑(3 * m * (9 * m)) by exact_mod_cast h
    push_cast
    simp only [show (27 : Int) = 3 * 9 from rfl,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  -- (3m+1)·2^86 = 3m·2^86 + 2^86
  have h_lhs : (3 * m + 1) * 2 ^ 86 = 3 * m * 2 ^ 86 + 2 ^ 86 := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
  rw [h_split, h_lhs]
  exact Nat.add_le_add_left (Nat.le_trans h_big h_prod) _

/-- The composition pipeline output never exceeds R_MAX.
    Proof has two cases:
    1. m ≤ M_TOP - 1: r_qc ≤ R + r_lo < (M_TOP-1)·2^86 + 2^86 + 8 = M_TOP·2^86 + 8 ≤ R_MAX.
    2. m = M_TOP: tight numerical analysis; if r_lo ≤ DELTA then trivial,
       if r_lo = DELTA + 1 then correction ≥ 1 compensates. -/
theorem r_qc_le_r_max (x_hi_1 x_lo_1 : Nat)
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
    r_qc ≤ R_MAX := by
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
  -- r_qc ≤ R + r_lo (correction ≥ 0)
  have h_rqc_le : R + r_lo - c ≤ R + r_lo := Nat.sub_le _ _
  -- ======== Step 3: Case split on m < M_TOP vs m ≥ M_TOP ========
  by_cases hm_lt_top : m < M_TOP
  · -- ======== Case A: m ≤ M_TOP - 1 ========
    -- r_lo ≤ 2^86 + 8 via tight_numerator_bound
    have hr_lo_tight : r_lo ≤ 2 ^ 86 + 8 := by
      show (res * 2 ^ 86 + limb_hi) / d ≤ 2 ^ 86 + 8
      -- Suffices: numerator < (2^86 + 9) * d
      suffices h : res * 2 ^ 86 + limb_hi < (2 ^ 86 + 9) * d by
        exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hd_pos).mpr h)
      -- numerator < (3m² + 3m + 1) * 2^86
      have h_num : res * 2 ^ 86 + limb_hi < (3 * (m * m) + 3 * m + 1) * 2 ^ 86 := by
        calc res * 2 ^ 86 + limb_hi
            < res * 2 ^ 86 + 2 ^ 86 := by omega
          _ = (res + 1) * 2 ^ 86 := by rw [Nat.add_mul, Nat.one_mul]
          _ ≤ (3 * (m * m) + 3 * m + 1) * 2 ^ 86 :=
              Nat.mul_le_mul_right _ (Nat.succ_le_succ hres_bound)
      -- (2^86 + 9) * d = 2^86 * d + 9 * d = 3m² * 2^86 + 9 * 3m²
      -- (3m² + 3m + 1) * 2^86 = 3m² * 2^86 + (3m+1) * 2^86
      -- From tight_numerator_bound: (3m+1) * 2^86 ≤ 27m² = 9 * 3m² = 9 * d
      have h27 := tight_numerator_bound m hm_lo
      -- So (3m² + 3m + 1) * 2^86 ≤ 3m² * 2^86 + 9 * d = (2^86 + 9) * d
      -- 3m²·2^86 + 27m² = (2^86 + 9) · 3m² = (2^86 + 9) · d
      have h_rhs : 3 * (m * m) * 2 ^ 86 + 27 * (m * m) = (2 ^ 86 + 9) * d := by
        show 3 * (m * m) * 2 ^ 86 + 27 * (m * m) = (2 ^ 86 + 9) * (3 * (m * m))
        omega
      calc res * 2 ^ 86 + limb_hi
          < (3 * (m * m) + 3 * m + 1) * 2 ^ 86 := h_num
        _ = 3 * (m * m) * 2 ^ 86 + (3 * m + 1) * 2 ^ 86 := by
            -- (a + b) * c = a*c + b*c
            have : (3 * (m * m) + (3 * m + 1)) * 2 ^ 86 =
                3 * (m * m) * 2 ^ 86 + (3 * m + 1) * 2 ^ 86 :=
              Nat.add_mul _ _ _
            omega
        _ ≤ 3 * (m * m) * 2 ^ 86 + 27 * (m * m) := Nat.add_le_add_left h27 _
        _ = (2 ^ 86 + 9) * d := h_rhs
    -- R ≤ (M_TOP - 1) * 2^86
    have hR_le : R ≤ (M_TOP - 1) * 2 ^ 86 :=
      Nat.mul_le_mul_right _ (by omega : m ≤ M_TOP - 1)
    -- r_qc ≤ R + r_lo ≤ (M_TOP - 1) * 2^86 + 2^86 + 8 = M_TOP * 2^86 + 8
    have h_sum : R + r_lo ≤ M_TOP * 2 ^ 86 + 8 :=
      calc R + r_lo
          ≤ (M_TOP - 1) * 2 ^ 86 + (2 ^ 86 + 8) := Nat.add_le_add hR_le hr_lo_tight
        _ = M_TOP * 2 ^ 86 + 8 := by
            rw [show M_TOP * 2 ^ 86 = (M_TOP - 1) * 2 ^ 86 + 1 * 2 ^ 86 from by omega]
    -- M_TOP * 2^86 + 8 ≤ R_MAX (since delta ≥ 9)
    have h_delta : 9 ≤ R_MAX - M_TOP * 2 ^ 86 := (r_lo_max_at_m_top).2.2
    have h_top_le : M_TOP * 2 ^ 86 + 8 ≤ R_MAX := by omega
    calc R + r_lo - c ≤ R + r_lo := h_rqc_le
      _ ≤ M_TOP * 2 ^ 86 + 8 := h_sum
      _ ≤ R_MAX := h_top_le
  · -- ======== Case B: m ≥ M_TOP, hence m = M_TOP ========
    have hm_ge : M_TOP ≤ m := by omega
    -- w < 2^254
    have hw_hi : w < 2 ^ 254 := by
      show x_hi_1 / 4 < 2 ^ 254; unfold WORD_MOD at hxhi_hi; omega
    -- (M_TOP + 1)³ > 2^254 > w, so m ≤ M_TOP
    have hm_le : m ≤ M_TOP := by
      -- If m ≥ M_TOP + 1, then m³ ≥ (M_TOP+1)³ ≥ 2^254 > w, contradicting m = icbrt(w)
      by_cases hm_eq : m ≤ M_TOP
      · exact hm_eq
      · exfalso
        have : M_TOP + 1 ≤ m := by omega
        have : (M_TOP + 1) * (M_TOP + 1) * (M_TOP + 1) ≤ m * m * m := cube_monotone this
        have : m * m * m ≤ w := hcube_le_w
        have := m_top_cube_bounds.2
        omega
    have hm_eq : m = M_TOP := Nat.le_antisymm hm_le hm_ge
    -- Substitute m = M_TOP everywhere
    -- r_lo ≤ delta + 1 from r_lo_max_at_m_top
    have h_rtop := r_lo_max_at_m_top
    let delta := R_MAX - M_TOP * 2 ^ 86
    -- Bound r_lo using res ≤ 3m² + 3m and w < 2^254
    -- res = w - m³ < 2^254 - M_TOP³ ≤ res_max  (since w ≤ 2^254 - 1)
    have hres_le : res ≤ 2 ^ 254 - 1 - M_TOP * M_TOP * M_TOP := by
      show w - m * m * m ≤ 2 ^ 254 - 1 - M_TOP * M_TOP * M_TOP
      rw [hm_eq]; omega
    have hd_eq : d = 3 * (M_TOP * M_TOP) := by show 3 * (m * m) = 3 * (M_TOP * M_TOP); rw [hm_eq]
    have hr_lo_le : r_lo ≤ delta + 1 := by
      show (res * 2 ^ 86 + limb_hi) / d ≤ delta + 1
      -- numerator ≤ res_max * 2^86 + 2^86 - 1
      have h_num : res * 2 ^ 86 + limb_hi ≤
          (2 ^ 254 - 1 - M_TOP * M_TOP * M_TOP) * 2 ^ 86 + 2 ^ 86 - 1 := by
        have : limb_hi ≤ 2 ^ 86 - 1 := by omega
        calc res * 2 ^ 86 + limb_hi
            ≤ (2 ^ 254 - 1 - M_TOP * M_TOP * M_TOP) * 2 ^ 86 + (2 ^ 86 - 1) :=
              Nat.add_le_add (Nat.mul_le_mul_right _ hres_le) this
          _ = (2 ^ 254 - 1 - M_TOP * M_TOP * M_TOP) * 2 ^ 86 + 2 ^ 86 - 1 := by omega
      -- From h_rtop.1: (res_max * 2^86 + 2^86 - 1) / (3*(M_TOP*M_TOP)) ≤ delta + 1
      rw [hd_eq]
      exact Nat.le_trans (Nat.div_le_div_right h_num) h_rtop.1
    -- Case split: r_lo ≤ delta vs r_lo = delta + 1
    by_cases hr_lo_delta : r_lo ≤ delta
    · -- r_lo ≤ delta: r_qc ≤ R + r_lo ≤ M_TOP * 2^86 + delta = R_MAX
      have hR_eq : R = M_TOP * 2 ^ 86 := by show m * 2 ^ 86 = M_TOP * 2 ^ 86; rw [hm_eq]
      calc R + r_lo - c
          ≤ R + r_lo := h_rqc_le
        _ = M_TOP * 2 ^ 86 + r_lo := by rw [hR_eq]
        _ ≤ M_TOP * 2 ^ 86 + delta := Nat.add_le_add_left hr_lo_delta _
        _ = R_MAX := by unfold delta; omega
    · -- r_lo > delta, i.e. r_lo = delta + 1 (since r_lo ≤ delta + 1)
      have hr_lo_eq : r_lo = delta + 1 := by omega
      -- correction = r_lo² / R ≥ (delta+1)² / (M_TOP * 2^86) ≥ 1
      have hR_eq : R = M_TOP * 2 ^ 86 := by show m * 2 ^ 86 = M_TOP * 2 ^ 86; rw [hm_eq]
      have hc_ge1 : 1 ≤ c := by
        show 1 ≤ r_lo * r_lo / R
        rw [hr_lo_eq, hR_eq]
        exact h_rtop.2.1
      -- r_qc = R + r_lo - c ≤ R + (delta + 1) - 1 = R + delta = M_TOP * 2^86 + delta = R_MAX
      calc R + r_lo - c
          ≤ R + r_lo - 1 := Nat.sub_le_sub_left hc_ge1 (R + r_lo)
        _ = M_TOP * 2 ^ 86 + (delta + 1) - 1 := by rw [hR_eq, hr_lo_eq]
        _ = M_TOP * 2 ^ 86 + delta := by omega
        _ = R_MAX := by unfold delta; omega

-- ============================================================================
-- Helper: R + r_lo ≤ R_MAX + 1 (for strict cube bound when c ≥ 2)
-- ============================================================================

/-- The sum R + r_lo is at most R_MAX + 1. Combined with c ≥ 2, this gives
    r_qc = R + r_lo - c ≤ R_MAX - 1, so (r_qc + 1)³ ≤ R_MAX³ < WORD_MOD². -/
theorem r_plus_rlo_le_rmax_succ (x_hi_1 x_lo_1 : Nat)
    (hxhi_lo : 2 ^ 253 ≤ x_hi_1) (hxhi_hi : x_hi_1 < WORD_MOD)
    (hxlo : x_lo_1 < WORD_MOD) :
    let w := x_hi_1 / 4
    let m := icbrt w
    let res := w - m * m * m
    let d := 3 * (m * m)
    let limb_hi := (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172
    let r_lo := (res * 2 ^ 86 + limb_hi) / d
    let R := m * 2 ^ 86
    R + r_lo ≤ R_MAX + 1 := by
  simp only
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
  let m := icbrt (x_hi_1 / 4)
  let w := x_hi_1 / 4
  let res := w - m * m * m
  let d := 3 * (m * m)
  let limb_hi := (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172
  let r_lo := (res * 2 ^ 86 + limb_hi) / d
  let R := m * 2 ^ 86
  -- Case A: m < M_TOP → R + r_lo ≤ M_TOP*2^86 + 8 ≤ R_MAX ≤ R_MAX + 1
  -- Case B: m = M_TOP → R + r_lo ≤ M_TOP*2^86 + delta + 1 = R_MAX + 1
  by_cases hm_lt_top : m < M_TOP
  · -- Case A: reuse tight r_lo bound
    have hlimb_bound : limb_hi < 2 ^ 86 := by
      show (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172 < 2 ^ 86
      have : x_hi_1 % 4 < 4 := Nat.mod_lt _ (by omega)
      have : x_lo_1 / 2 ^ 172 < 2 ^ 84 := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 172)]
        calc x_lo_1 < WORD_MOD := hxlo
          _ = 2 ^ 84 * 2 ^ 172 := by unfold WORD_MOD; rw [← Nat.pow_add]
      have : (x_hi_1 % 4) * 2 ^ 84 < 2 ^ 86 :=
        calc (x_hi_1 % 4) * 2 ^ 84 < 4 * 2 ^ 84 :=
                Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos 84)
          _ = 2 ^ 86 := by rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add]
      omega
    have hr_lo_tight : r_lo ≤ 2 ^ 86 + 8 := by
      show (res * 2 ^ 86 + limb_hi) / d ≤ 2 ^ 86 + 8
      suffices h : res * 2 ^ 86 + limb_hi < (2 ^ 86 + 9) * d by
        exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hd_pos).mpr h)
      have h_num : res * 2 ^ 86 + limb_hi < (3 * (m * m) + 3 * m + 1) * 2 ^ 86 := by
        calc res * 2 ^ 86 + limb_hi
            < res * 2 ^ 86 + 2 ^ 86 := by omega
          _ = (res + 1) * 2 ^ 86 := by rw [Nat.add_mul, Nat.one_mul]
          _ ≤ (3 * (m * m) + 3 * m + 1) * 2 ^ 86 :=
              Nat.mul_le_mul_right _ (Nat.succ_le_succ hres_bound)
      have h27 := tight_numerator_bound m hm_lo
      have h_rhs : 3 * (m * m) * 2 ^ 86 + 27 * (m * m) = (2 ^ 86 + 9) * d := by
        show 3 * (m * m) * 2 ^ 86 + 27 * (m * m) = (2 ^ 86 + 9) * (3 * (m * m)); omega
      calc res * 2 ^ 86 + limb_hi
          < (3 * (m * m) + 3 * m + 1) * 2 ^ 86 := h_num
        _ = 3 * (m * m) * 2 ^ 86 + (3 * m + 1) * 2 ^ 86 := by
            have : (3 * (m * m) + (3 * m + 1)) * 2 ^ 86 =
                3 * (m * m) * 2 ^ 86 + (3 * m + 1) * 2 ^ 86 := Nat.add_mul _ _ _
            omega
        _ ≤ 3 * (m * m) * 2 ^ 86 + 27 * (m * m) := Nat.add_le_add_left h27 _
        _ = (2 ^ 86 + 9) * d := h_rhs
    have hR_le : R ≤ (M_TOP - 1) * 2 ^ 86 :=
      Nat.mul_le_mul_right _ (by omega : m ≤ M_TOP - 1)
    have h_delta : 9 ≤ R_MAX - M_TOP * 2 ^ 86 := (r_lo_max_at_m_top).2.2
    calc R + r_lo
        ≤ (M_TOP - 1) * 2 ^ 86 + (2 ^ 86 + 8) := Nat.add_le_add hR_le hr_lo_tight
      _ = M_TOP * 2 ^ 86 + 8 := by omega
      _ ≤ R_MAX := by omega
      _ ≤ R_MAX + 1 := Nat.le_succ _
  · -- Case B: m = M_TOP
    have hm_ge : M_TOP ≤ m := by omega
    have hw_hi : w < 2 ^ 254 := by show x_hi_1 / 4 < 2 ^ 254; unfold WORD_MOD at hxhi_hi; omega
    have hm_le : m ≤ M_TOP := by
      by_cases hm_eq : m ≤ M_TOP
      · exact hm_eq
      · exfalso
        have : M_TOP + 1 ≤ m := by omega
        have : (M_TOP + 1) * (M_TOP + 1) * (M_TOP + 1) ≤ m * m * m := cube_monotone this
        have : m * m * m ≤ w := hcube_le_w
        have := m_top_cube_bounds.2; omega
    have hm_eq : m = M_TOP := Nat.le_antisymm hm_le hm_ge
    have h_rtop := r_lo_max_at_m_top
    let delta := R_MAX - M_TOP * 2 ^ 86
    have hlimb_bound : limb_hi < 2 ^ 86 := by
      show (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172 < 2 ^ 86
      have : x_hi_1 % 4 < 4 := Nat.mod_lt _ (by omega)
      have : x_lo_1 / 2 ^ 172 < 2 ^ 84 := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 172)]
        calc x_lo_1 < WORD_MOD := hxlo
          _ = 2 ^ 84 * 2 ^ 172 := by unfold WORD_MOD; rw [← Nat.pow_add]
      have : (x_hi_1 % 4) * 2 ^ 84 < 2 ^ 86 :=
        calc (x_hi_1 % 4) * 2 ^ 84 < 4 * 2 ^ 84 :=
                Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos 84)
          _ = 2 ^ 86 := by rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add]
      omega
    have hres_le : res ≤ 2 ^ 254 - 1 - M_TOP * M_TOP * M_TOP := by
      show w - m * m * m ≤ 2 ^ 254 - 1 - M_TOP * M_TOP * M_TOP; rw [hm_eq]; omega
    have hd_eq : d = 3 * (M_TOP * M_TOP) := by
      show 3 * (m * m) = 3 * (M_TOP * M_TOP); rw [hm_eq]
    have hr_lo_le : r_lo ≤ delta + 1 := by
      show (res * 2 ^ 86 + limb_hi) / d ≤ delta + 1
      have h_num : res * 2 ^ 86 + limb_hi ≤
          (2 ^ 254 - 1 - M_TOP * M_TOP * M_TOP) * 2 ^ 86 + 2 ^ 86 - 1 := by
        have : limb_hi ≤ 2 ^ 86 - 1 := by omega
        calc res * 2 ^ 86 + limb_hi
            ≤ (2 ^ 254 - 1 - M_TOP * M_TOP * M_TOP) * 2 ^ 86 + (2 ^ 86 - 1) :=
              Nat.add_le_add (Nat.mul_le_mul_right _ hres_le) this
          _ = (2 ^ 254 - 1 - M_TOP * M_TOP * M_TOP) * 2 ^ 86 + 2 ^ 86 - 1 := by omega
      rw [hd_eq]; exact Nat.le_trans (Nat.div_le_div_right h_num) h_rtop.1
    have hR_eq : R = M_TOP * 2 ^ 86 := by show m * 2 ^ 86 = M_TOP * 2 ^ 86; rw [hm_eq]
    calc R + r_lo
        = M_TOP * 2 ^ 86 + r_lo := by rw [hR_eq]
      _ ≤ M_TOP * 2 ^ 86 + (delta + 1) := Nat.add_le_add_left hr_lo_le _
      _ = R_MAX + 1 := by unfold delta; omega


end Cbrt512Spec

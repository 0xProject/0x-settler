/-
  Base case: model_cbrtBaseCase_evm(x_hi_1) returns (r_hi, res, d) where
    r_hi = icbrt(x_hi_1 / 4)
    res = x_hi_1 / 4 - r_hi³
    d = 3 * r_hi²
-/
import Cbrt512Proof.GeneratedCbrt512Model
import Cbrt512Proof.EvmBridge
import CbrtProof.CbrtCorrect
import CbrtProof.CertifiedChain
import CbrtProof.FiniteCert
import CbrtProof.Wiring

namespace Cbrt512Spec

open Cbrt512GeneratedModel
open CbrtCertified
open CbrtCert

-- ============================================================================
-- NR step EVM bridge
-- ============================================================================

/-- model_cbrtNRStep_evm(x, r) = cbrtStep(x, r) when intermediate values fit in uint256. -/
theorem model_cbrtNRStep_evm_eq_cbrtStep (x r : Nat)
    (hx : x < WORD_MOD) (hr : r < WORD_MOD)
    (hrr : r * r < WORD_MOD)
    (hsum : x / (r * r) + 2 * r < WORD_MOD) :
    model_cbrtNRStep_evm x r = cbrtStep x r := by
  unfold model_cbrtNRStep_evm cbrtStep
  simp only [u256, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hr]
  have hmul_rr : evmMul r r = r * r := by
    unfold evmMul u256; simp [Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hrr]
  have hdiv_xrr : evmDiv x (evmMul r r) = x / (r * r) := by
    rw [hmul_rr]; unfold evmDiv u256
    rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hrr]
    by_cases hrr0 : r * r = 0
    · simp [hrr0]
    · simp [hrr0, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self x _) hx)]
  have hdiv_lt : x / (r * r) < WORD_MOD :=
    Nat.lt_of_le_of_lt (Nat.div_le_self x _) hx
  have hadd1_lt : x / (r * r) + r < WORD_MOD := by omega
  have hadd1 : evmAdd (evmDiv x (evmMul r r)) r = x / (r * r) + r := by
    rw [hdiv_xrr]; unfold evmAdd u256
    simp [Nat.mod_eq_of_lt hdiv_lt, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hadd1_lt]
  have hadd2 : evmAdd (evmAdd (evmDiv x (evmMul r r)) r) r = x / (r * r) + 2 * r := by
    rw [hadd1]; unfold evmAdd u256
    rw [Nat.mod_eq_of_lt hadd1_lt, Nat.mod_eq_of_lt hr]
    rw [show x / (r * r) + r + r = x / (r * r) + 2 * r from by omega]
    exact Nat.mod_eq_of_lt hsum
  have h3_wm : (3 : Nat) < WORD_MOD := by unfold WORD_MOD; omega
  rw [hadd2]; unfold evmDiv u256
  simp [Nat.mod_eq_of_lt hsum, Nat.mod_eq_of_lt h3_wm]

-- ============================================================================
-- 6-step chain helper
-- ============================================================================

/-- Chain step_from_bound 5 times then conclude z6 ≤ m+1. -/
private theorem chain_6steps_upper (w m lo : Nat) (s d1 : Nat)
    (hm2 : 2 ≤ m) (hloPos : 0 < lo) (hlo : lo ≤ m) (hsPos : 0 < s)
    (hmlo : m * m * m ≤ w) (hmhi : w < (m + 1) * (m + 1) * (m + 1))
    (hd1 : cbrtStep w s - m ≤ d1) (h2d1 : 2 * d1 ≤ m)
    (h2d2 : 2 * nextD lo d1 ≤ lo) (h2d3 : 2 * nextD lo (nextD lo d1) ≤ lo)
    (h2d4 : 2 * nextD lo (nextD lo (nextD lo d1)) ≤ lo)
    (h2d5 : 2 * nextD lo (nextD lo (nextD lo (nextD lo d1))) ≤ lo)
    (hd6_le_1 : nextD lo (nextD lo (nextD lo (nextD lo (nextD lo d1)))) ≤ 1) :
    run6From w s ≤ m + 1 := by
  let z1 := cbrtStep w s
  let z2 := cbrtStep w z1
  let z3 := cbrtStep w z2
  let z4 := cbrtStep w z3
  let z5 := cbrtStep w z4
  have hmz1 : m ≤ z1 := cbrt_step_floor_bound w s m hsPos hmlo
  have hmz2 : m ≤ z2 := cbrt_step_floor_bound w z1 m (by omega) hmlo
  have hmz3 : m ≤ z3 := cbrt_step_floor_bound w z2 m (by omega) hmlo
  have hmz4 : m ≤ z4 := cbrt_step_floor_bound w z3 m (by omega) hmlo
  have hmz5 : m ≤ z5 := cbrt_step_floor_bound w z4 m (by omega) hmlo
  have hd2 : z2 - m ≤ nextD lo d1 :=
    step_from_bound w m lo z1 d1 hm2 hloPos hlo hmhi hmz1 hd1 h2d1
  have hd3 : z3 - m ≤ nextD lo (nextD lo d1) :=
    step_from_bound w m lo z2 (nextD lo d1) hm2 hloPos hlo hmhi hmz2 hd2 (by omega)
  have hd4 : z4 - m ≤ nextD lo (nextD lo (nextD lo d1)) :=
    step_from_bound w m lo z3 _ hm2 hloPos hlo hmhi hmz3 hd3 (by omega)
  have hd5 : z5 - m ≤ nextD lo (nextD lo (nextD lo (nextD lo d1))) :=
    step_from_bound w m lo z4 _ hm2 hloPos hlo hmhi hmz4 hd4 (by omega)
  have hd6 : cbrtStep w z5 - m ≤ nextD lo (nextD lo (nextD lo (nextD lo (nextD lo d1)))) :=
    step_from_bound w m lo z5 _ hm2 hloPos hlo hmhi hmz5 hd5 (by omega)
  -- cbrtStep w z5 - m ≤ 1
  have hd6_1 : cbrtStep w z5 - m ≤ 1 := Nat.le_trans hd6 hd6_le_1
  -- run6From is definitionally cbrtStep applied to run5From which equals z5
  have : run6From w s = cbrtStep w z5 := rfl
  omega

-- ============================================================================
-- Per-octave NR convergence
-- ============================================================================

/-- Helper: establish lo ≤ m from lo³ ≤ 2^k ≤ w and m = icbrt(w). -/
private theorem lo_le_icbrt_of_cube_le_pow (w lo : Nat) (k : Nat)
    (hlo_cube : lo * lo * lo ≤ 2 ^ k) (hw_lo : 2 ^ k ≤ w) :
    lo ≤ icbrt w := by
  have hlo_w : lo * lo * lo ≤ w := Nat.le_trans hlo_cube hw_lo
  by_cases h : lo ≤ icbrt w; · exact h
  · exfalso
    have : icbrt w + 1 ≤ lo := by omega
    exact Nat.lt_irrefl w (Nat.lt_of_lt_of_le (icbrt_lt_succ_cube w)
      (Nat.le_trans (cube_monotone this) hlo_w))

/-- Helper: establish m ≤ hi from (hi+1)³ > 2^(k+1) and w < 2^(k+1). -/
private theorem icbrt_le_hi_of_pow_lt_cube (w hi : Nat) (k : Nat)
    (hhi_cube : 2 ^ (k + 1) ≤ (hi + 1) * (hi + 1) * (hi + 1)) (hw_hi : w < 2 ^ (k + 1)) :
    icbrt w ≤ hi := by
  by_cases h : icbrt w ≤ hi; · exact h
  · exfalso
    have : hi + 1 ≤ icbrt w := by omega
    have := cube_monotone this
    exact Nat.lt_irrefl w (Nat.lt_of_lt_of_le hw_hi
      (Nat.le_trans hhi_cube (Nat.le_trans this (icbrt_cube_le w))))

/-- The 6 NR steps from the fixed seed converge to within ±1 of icbrt(w)
    for w ∈ [2^251, 2^254). -/
theorem baseCase_NR_within_1ulp (w : Nat)
    (hw_lo : 2 ^ 251 ≤ w) (hw_hi : w < 2 ^ 254) :
    let m := icbrt w
    let z := run6From w 22141993662453218394297550
    m ≤ z ∧ z ≤ m + 1 := by
  simp only
  let s : Nat := 22141993662453218394297550
  let m := icbrt w
  have hmlo : m * m * m ≤ w := icbrt_cube_le w
  have hmhi : w < (m + 1) * (m + 1) * (m + 1) := icbrt_lt_succ_cube w
  have hsPos : 0 < s := by omega
  have hw_pos : 0 < w := by omega
  -- Lower bound
  have hmz : m ≤ run6From w s := by
    unfold run6From
    exact cbrt_step_floor_bound w _ m
      (cbrtStep_pos w _ hw_pos
        (cbrtStep_pos w _ hw_pos
          (cbrtStep_pos w _ hw_pos
            (cbrtStep_pos w _ hw_pos
              (cbrtStep_pos w _ hw_pos hsPos)))))
      hmlo
  refine ⟨hmz, ?_⟩
  -- Case split on octave
  by_cases h252 : w < 2 ^ 252
  · -- Octave 251: w ∈ [2^251, 2^252)
    -- lo = 15352400942462240883748044, hi = 19342813113834066795298815
    let lo : Nat := 15352400942462240883748044
    have hlo : lo ≤ m := lo_le_icbrt_of_cube_le_pow w lo 251 (by native_decide) hw_lo
    have hhi : m ≤ 19342813113834066795298815 :=
      icbrt_le_hi_of_pow_lt_cube w 19342813113834066795298815 251 (by native_decide) h252
    have hm2 : 2 ≤ m := by omega
    -- d1 bound
    have hd1 : cbrtStep w s - m ≤ 1994218922075376856504634 := by
      have h := cbrt_d1_bound w m s lo 19342813113834066795298815 hsPos hmlo hmhi hlo hhi
      have : max (s - lo) (19342813113834066795298815 - s) = 6789592719990977510549506 := by
        native_decide
      rw [this] at h
      have : (6789592719990977510549506 * 6789592719990977510549506 *
          (19342813113834066795298815 + 2 * s) + 3 * 19342813113834066795298815 *
          (19342813113834066795298815 + 1)) / (3 * (s * s)) =
          1994218922075376856504634 := by native_decide
      omega
    exact chain_6steps_upper w m lo s 1994218922075376856504634
      hm2 (by omega : 0 < lo) hlo hsPos hmlo hmhi hd1
      (Nat.le_trans (by native_decide : 2 * 1994218922075376856504634 ≤ lo) hlo)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  · by_cases h253 : w < 2 ^ 253
    · -- Octave 252: w ∈ [2^252, 2^253)
      let lo : Nat := 19342813113834066795298816
      have hlo : lo ≤ m := lo_le_icbrt_of_cube_le_pow w lo 252 (by native_decide) (by omega)
      have hhi : m ≤ 24370417406302138235346347 :=
        icbrt_le_hi_of_pow_lt_cube w 24370417406302138235346347 252 (by native_decide) h253
      have hm2 : 2 ≤ m := by omega
      have hd1 : cbrtStep w s - m ≤ 365742585066387069963242 := by
        have h := cbrt_d1_bound w m s lo 24370417406302138235346347 hsPos hmlo hmhi hlo hhi
        have : max (s - lo) (24370417406302138235346347 - s) =
            2799180548619151598998734 := by native_decide
        rw [this] at h
        have : (2799180548619151598998734 * 2799180548619151598998734 *
            (24370417406302138235346347 + 2 * s) + 3 * 24370417406302138235346347 *
            (24370417406302138235346347 + 1)) / (3 * (s * s)) =
            365742585066387069963242 := by native_decide
        omega
      exact chain_6steps_upper w m lo s 365742585066387069963242
        hm2 (by omega : 0 < lo) hlo hsPos hmlo hmhi hd1
        (Nat.le_trans (by native_decide : 2 * 365742585066387069963242 ≤ lo) hlo)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    · -- Octave 253: w ∈ [2^253, 2^254)
      let lo : Nat := 24370417406302138235346347
      have hlo : lo ≤ m := lo_le_icbrt_of_cube_le_pow w lo 253 (by native_decide) (by omega)
      have hhi : m ≤ 30704801884924481767496089 :=
        icbrt_le_hi_of_pow_lt_cube w 30704801884924481767496089 253 (by native_decide) hw_hi
      have hm2 : 2 ≤ m := by omega
      have hd1 : cbrtStep w s - m ≤ 3738299367780524623633435 := by
        have h := cbrt_d1_bound w m s lo 30704801884924481767496089 hsPos hmlo hmhi hlo hhi
        have : max (s - lo) (30704801884924481767496089 - s) =
            8562808222471263373198539 := by native_decide
        rw [this] at h
        have : (8562808222471263373198539 * 8562808222471263373198539 *
            (30704801884924481767496089 + 2 * s) + 3 * 30704801884924481767496089 *
            (30704801884924481767496089 + 1)) / (3 * (s * s)) =
            3738299367780524623633435 := by native_decide
        omega
      exact chain_6steps_upper w m lo s 3738299367780524623633435
        hm2 (by omega : 0 < lo) hlo hsPos hmlo hmhi hd1
        (Nat.le_trans (by native_decide : 2 * 3738299367780524623633435 ≤ lo) hlo)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)

/-- On a perfect cube w = m³ with m ≥ 2^83, the 6 NR steps give exactly m. -/
theorem baseCase_NR_exact_on_perfect_cube (m : Nat)
    (hm_lo : 2 ^ 83 ≤ m) (hm_hi : m < 2 ^ 85)
    (hw_range : m * m * m < 2 ^ 254) :
    run6From (m * m * m) 22141993662453218394297550 = m := by
  sorry

-- ============================================================================
-- Base case EVM bridge
-- ============================================================================

/-- One NR step matches cbrtStep and the result stays below 2^88. -/
private theorem nr_step_ok (w z : Nat) (hw : w < 2 ^ 254)
    (hz_lo : 2 ^ 83 ≤ z) (hz_hi : z < 2 ^ 88) :
    model_cbrtNRStep_evm w z = cbrtStep w z ∧ cbrtStep w z < 2 ^ 88 := by
  have hw_wm : w < WORD_MOD := by unfold WORD_MOD; omega
  have hz_wm : z < WORD_MOD := by unfold WORD_MOD; omega
  have hzz_wm : z * z < WORD_MOD := by
    calc z * z
        < 2 ^ 88 * 2 ^ 88 := Nat.lt_of_lt_of_le
            (Nat.mul_lt_mul_of_pos_left hz_hi (by omega))
            (Nat.mul_le_mul_right _ (Nat.le_of_lt hz_hi))
      _ = 2 ^ 176 := by rw [← Nat.pow_add]
      _ < WORD_MOD := by unfold WORD_MOD; exact Nat.pow_lt_pow_right (by omega) (by omega)
  have hzz_ge : 2 ^ 166 ≤ z * z :=
    calc 2 ^ 166 = 2 ^ 83 * 2 ^ 83 := by rw [← Nat.pow_add]
      _ ≤ z * z := Nat.mul_le_mul hz_lo hz_lo
  have hdiv_lt : w / (z * z) < 2 ^ 88 :=
    (Nat.div_lt_iff_lt_mul (by omega : 0 < z * z)).mpr
      (calc w < 2 ^ 254 := hw
        _ = 2 ^ 88 * 2 ^ 166 := by rw [← Nat.pow_add]
        _ ≤ 2 ^ 88 * (z * z) := Nat.mul_le_mul_left _ hzz_ge)
  have hsum : w / (z * z) + 2 * z < WORD_MOD := by
    have : w / (z * z) ≤ w := Nat.div_le_self _ _; unfold WORD_MOD; omega
  exact ⟨model_cbrtNRStep_evm_eq_cbrtStep w z hw_wm hz_wm hzz_wm hsum,
    (Nat.div_lt_iff_lt_mul (by omega : (0 : Nat) < 3)).mpr (by omega)⟩

/-- The base case EVM model matches the 256-bit cbrt for the normalized input. -/
theorem model_cbrtBaseCase_evm_correct (x_hi_1 : Nat)
    (hx_lo : 2 ^ 253 ≤ x_hi_1) (hx_hi : x_hi_1 < WORD_MOD) :
    let w := x_hi_1 / 4
    let m := icbrt w
    let bc := model_cbrtBaseCase_evm x_hi_1
    bc.1 = m ∧
    bc.2.1 = w - m * m * m ∧
    bc.2.2 = 3 * (m * m) ∧
    2 ^ 83 ≤ m ∧ m < 2 ^ 85 ∧
    m * m * m ≤ w ∧
    w - m * m * m ≤ 3 * (m * m) + 3 * m ∧
    m < WORD_MOD ∧
    m * m < WORD_MOD ∧
    3 * (m * m) < WORD_MOD ∧
    3 * (m * m) > 0 := by
  simp only
  let w := x_hi_1 / 4
  let m := icbrt w
  -- ======== Range bounds ========
  have hw_lo : 2 ^ 251 ≤ w := by show 2 ^ 251 ≤ x_hi_1 / 4; omega
  have hw_hi : w < 2 ^ 254 := by
    show x_hi_1 / 4 < 2 ^ 254; unfold WORD_MOD at hx_hi; omega
  have hw_wm : w < WORD_MOD := by show x_hi_1 / 4 < WORD_MOD; unfold WORD_MOD; omega
  have hm_lo : 2 ^ 83 ≤ m :=
    lo_le_icbrt_of_cube_le_pow w (2 ^ 83) 251 (by native_decide) hw_lo
  have hm_hi : m < 2 ^ 85 := by
    show icbrt w < 2 ^ 85
    have := icbrt_le_hi_of_pow_lt_cube w (2 ^ 85 - 1) 253 (by native_decide) hw_hi
    omega
  have hm_wm : m < WORD_MOD := by unfold WORD_MOD; omega
  have hm2_le : m * m ≤ (2 ^ 85 - 1) * (2 ^ 85 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hm2_wm : m * m < WORD_MOD := by
    have : (2 ^ 85 - 1) * (2 ^ 85 - 1) < WORD_MOD := by unfold WORD_MOD; native_decide
    omega
  have hm3_le : m * m * m ≤ (2 ^ 85 - 1) * (2 ^ 85 - 1) * (2 ^ 85 - 1) :=
    Nat.mul_le_mul hm2_le (by omega)
  have hm3_wm : m * m * m < WORD_MOD := by
    have : (2 ^ 85 - 1) * (2 ^ 85 - 1) * (2 ^ 85 - 1) < WORD_MOD := by
      unfold WORD_MOD; native_decide
    omega
  have h3m2_wm : 3 * (m * m) < WORD_MOD := by omega
  have h3m2_pos : 3 * (m * m) > 0 := by
    have : 0 < m * m := Nat.mul_pos (by omega) (by omega); omega
  have hmcube_le : m * m * m ≤ w := icbrt_cube_le w
  have hmsucc_gt : w < (m + 1) * (m + 1) * (m + 1) := icbrt_lt_succ_cube w
  -- Residue bound: w - m³ ≤ 3m² + 3m from (m+1)³ = m³ + 3m² + 3m + 1
  have hres_bound : w - m * m * m ≤ 3 * (m * m) + 3 * m := by
    suffices heq : (m + 1) * (m + 1) * (m + 1) = m * m * m + 3 * (m * m) + 3 * m + 1 by omega
    suffices hi : (↑((m + 1) * (m + 1) * (m + 1)) : Int) =
        ↑(m * m * m + 3 * (m * m) + 3 * m + 1) by exact_mod_cast hi
    push_cast; simp [Int.add_mul, Int.mul_add, Int.mul_one, Int.one_mul]; omega
  -- ======== NR chain: 6 steps ========
  let s := (22141993662453218394297550 : Nat)
  have hs_lo : 2 ^ 83 ≤ s := by native_decide
  have hs_hi : s < 2 ^ 88 := by native_decide
  let z1 := cbrtStep w s
  let z2 := cbrtStep w z1
  let z3 := cbrtStep w z2
  let z4 := cbrtStep w z3
  let z5 := cbrtStep w z4
  let z6 := cbrtStep w z5
  have h_nr1 := nr_step_ok w s hw_hi hs_lo hs_hi
  have h_lo1 : 2 ^ 83 ≤ z1 :=
    Nat.le_trans hm_lo (cbrt_step_floor_bound w s m (by omega) hmcube_le)
  have h_nr2 := nr_step_ok w z1 hw_hi h_lo1 h_nr1.2
  have h_lo2 : 2 ^ 83 ≤ z2 :=
    Nat.le_trans hm_lo (cbrt_step_floor_bound w z1 m (by omega) hmcube_le)
  have h_nr3 := nr_step_ok w z2 hw_hi h_lo2 h_nr2.2
  have h_lo3 : 2 ^ 83 ≤ z3 :=
    Nat.le_trans hm_lo (cbrt_step_floor_bound w z2 m (by omega) hmcube_le)
  have h_nr4 := nr_step_ok w z3 hw_hi h_lo3 h_nr3.2
  have h_lo4 : 2 ^ 83 ≤ z4 :=
    Nat.le_trans hm_lo (cbrt_step_floor_bound w z3 m (by omega) hmcube_le)
  have h_nr5 := nr_step_ok w z4 hw_hi h_lo4 h_nr4.2
  have h_lo5 : 2 ^ 83 ≤ z5 :=
    Nat.le_trans hm_lo (cbrt_step_floor_bound w z4 m (by omega) hmcube_le)
  have h_nr6 := nr_step_ok w z5 hw_hi h_lo5 h_nr5.2
  -- ======== NR convergence ========
  have hnr_bounds := baseCase_NR_within_1ulp w hw_lo hw_hi
  -- z6 = run6From w s definitionally
  have hm_le_z6 : m ≤ z6 := hnr_bounds.1
  have hz6_le_m1 : z6 ≤ m + 1 := hnr_bounds.2
  -- ======== Post-NR EVM bounds ========
  have hz6_wm : z6 < WORD_MOD := by unfold WORD_MOD; omega
  have hz6_le_85 : z6 ≤ 2 ^ 85 := by omega
  have hz6z6_le : z6 * z6 ≤ (2 ^ 85) * (2 ^ 85) :=
    Nat.mul_le_mul hz6_le_85 hz6_le_85
  have hz6z6_wm : z6 * z6 < WORD_MOD := by
    have : (2 : Nat) ^ 85 * 2 ^ 85 = 2 ^ 170 := by rw [← Nat.pow_add]
    unfold WORD_MOD; omega
  have hz6z6z6_le : z6 * z6 * z6 ≤ (2 ^ 85) * (2 ^ 85) * (2 ^ 85) :=
    Nat.mul_le_mul hz6z6_le hz6_le_85
  have hz6z6z6_wm : z6 * z6 * z6 < WORD_MOD := by
    have : (2 : Nat) ^ 85 * 2 ^ 85 * 2 ^ 85 = 2 ^ 255 := by
      rw [show (2 : Nat) ^ 85 * 2 ^ 85 = 2 ^ 170 from by rw [← Nat.pow_add], ← Nat.pow_add]
    unfold WORD_MOD; omega
  -- ======== Shift lemma ========
  have hshift : evmShr (evmAnd (evmAnd 2 255) 255) x_hi_1 = w := by
    have : evmAnd (evmAnd 2 255) 255 = 2 := by native_decide
    rw [this]; exact evmShr_eq' 2 x_hi_1 (by omega) hx_hi
  -- ======== EVM bridge: z6² and z6³ ========
  have hevmMul_z6z6 : evmMul z6 z6 = z6 * z6 := by
    rw [evmMul_eq' z6 z6 hz6_wm hz6_wm, Nat.mod_eq_of_lt hz6z6_wm]
  have hevmMul_z6sq_z6 : evmMul (z6 * z6) z6 = z6 * z6 * z6 := by
    rw [evmMul_eq' (z6 * z6) z6 hz6z6_wm hz6_wm, Nat.mod_eq_of_lt hz6z6z6_wm]
  have hevmGt_z6cube_w : evmGt (z6 * z6 * z6) w = if z6 * z6 * z6 > w then 1 else 0 :=
    evmGt_eq' (z6 * z6 * z6) w hz6z6z6_wm hw_wm
  -- ======== EVM bridge: operations on m ========
  have hmm : evmMul m m = m * m := by
    rw [evmMul_eq' m m hm_wm hm_wm, Nat.mod_eq_of_lt hm2_wm]
  have hm2m : evmMul (m * m) m = m * m * m := by
    rw [evmMul_eq' (m * m) m hm2_wm hm_wm, Nat.mod_eq_of_lt hm3_wm]
  have hsubwm3 : evmSub w (m * m * m) = w - m * m * m :=
    evmSub_eq_of_le w (m * m * m) hw_wm hmcube_le
  have hm23 : evmMul (m * m) 3 = 3 * (m * m) := by
    rw [evmMul_eq' (m * m) 3 hm2_wm (show (3:Nat) < WORD_MOD by unfold WORD_MOD; omega),
        show (m * m) * 3 = 3 * (m * m) from Nat.mul_comm _ _,
        Nat.mod_eq_of_lt h3m2_wm]
  -- ======== Suffices: model = (m, w - m³, 3m²) ========
  suffices hcomp : model_cbrtBaseCase_evm x_hi_1 = (m, w - m * m * m, 3 * (m * m)) by
    rw [hcomp]
    exact ⟨rfl, rfl, rfl, hm_lo, hm_hi, hmcube_le, hres_bound,
           hm_wm, hm2_wm, h3m2_wm, h3m2_pos⟩
  -- ======== Unfold model and simplify ========
  -- Use rw (not simp only) because rw does definitional matching through let-bindings
  unfold model_cbrtBaseCase_evm
  simp only [u256_id' x_hi_1 hx_hi, hshift]
  -- NR chain
  rw [h_nr1.1, h_nr2.1, h_nr3.1, h_nr4.1, h_nr5.1, h_nr6.1]
  -- Post-NR EVM: z6² and z6³
  rw [hevmMul_z6z6, hevmMul_z6sq_z6, hevmGt_z6cube_w]
  -- ======== Case split on floor correction ========
  split
  · -- Case z6³ > w: z6 = m+1, correction gives m
    next hgt =>
    have hz6_eq : z6 = m + 1 := by
      rcases (show z6 = m ∨ z6 = m + 1 from by omega) with h | h
      · exfalso
        have h1 : z6 * z6 * z6 ≤ w := by rw [h]; exact hmcube_le
        exact Nat.lt_irrefl w (Nat.lt_of_lt_of_le hgt h1)
      · exact h
    have hcorr : evmSub z6 1 = m := by
      rw [evmSub_eq_of_le z6 1 hz6_wm (by omega), hz6_eq]; omega
    rw [hcorr, hmm, hm2m, hsubwm3, hm23]
  · -- Case z6³ ≤ w: z6 = m, no correction needed
    next hle =>
    have hz6_eq : z6 = m := by
      rcases (show z6 = m ∨ z6 = m + 1 from by omega) with h | h
      · exact h
      · exfalso
        have h1 : z6 * z6 * z6 > w := by
          show w < z6 * z6 * z6; rw [h]; exact hmsucc_gt
        exact hle h1
    have hcorr : evmSub z6 0 = m := by
      rw [evmSub_eq_of_le z6 0 hz6_wm (by omega), Nat.sub_zero, hz6_eq]
    rw [hcorr, hmm, hm2m, hsubwm3, hm23]

end Cbrt512Spec

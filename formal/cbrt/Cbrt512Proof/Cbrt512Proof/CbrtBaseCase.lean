/-
  Base case: model_cbrtBaseCase_evm(x_hi_1) returns (r_hi, res, d) where
    r_hi = icbrt(x_hi_1 / 4)
    res = x_hi_1 / 4 - r_hi³
    d = 3 * r_hi²
-/
import Cbrt512Proof.GeneratedCbrt512Model
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
  sorry

end Cbrt512Spec

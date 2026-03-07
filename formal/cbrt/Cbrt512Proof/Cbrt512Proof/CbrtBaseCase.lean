/-
  Base case: model_cbrtBaseCase_evm(x_hi_1) returns (r_hi, res, d) where
    r_hi = icbrt(x_hi_1 / 4)
    res = x_hi_1 / 4 - r_hi³
    d = 3 * r_hi²
-/
import Cbrt512Proof.GeneratedCbrt512Model
import Cbrt512Proof.EvmBridge
import Cbrt512Proof.CbrtNumericCerts
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
    · simp [hrr0]
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
-- Per-octave NR convergence helper
-- ============================================================================

/-- Parameterized octave convergence: combines d1 bound from cbrt_d1_bound
    with chain_6steps_upper to show run6From w s ≤ m + 1 for a given octave. -/
private theorem octave_upper (w m s lo hi gap d1 : Nat)
    (hsPos : 0 < s)
    (hmlo : m * m * m ≤ w) (hmhi : w < (m + 1) * (m + 1) * (m + 1))
    (hlo : lo ≤ m) (hhi : m ≤ hi) (hm2 : 2 ≤ m) (hloPos : 0 < lo)
    (hgap_eq : max (s - lo) (hi - s) = gap)
    (hd1_formula : (gap * gap * (hi + 2 * s) + 3 * hi * (hi + 1)) / (3 * (s * s)) = d1)
    (h2d1_lo : 2 * d1 ≤ lo)
    (h2d2 : 2 * nextD lo d1 ≤ lo)
    (h2d3 : 2 * nextD lo (nextD lo d1) ≤ lo)
    (h2d4 : 2 * nextD lo (nextD lo (nextD lo d1)) ≤ lo)
    (h2d5 : 2 * nextD lo (nextD lo (nextD lo (nextD lo d1))) ≤ lo)
    (hd6_le1 : nextD lo (nextD lo (nextD lo (nextD lo (nextD lo d1)))) ≤ 1) :
    run6From w s ≤ m + 1 := by
  have hd1 : cbrtStep w s - m ≤ d1 := by
    have h := cbrt_d1_bound w m s lo hi hsPos hmlo hmhi hlo hhi
    rw [hgap_eq] at h; simpa [hd1_formula] using h
  exact chain_6steps_upper w m lo s d1 hm2 hloPos hlo hsPos hmlo hmhi hd1
    (Nat.le_trans h2d1_lo hlo) h2d2 h2d3 h2d4 h2d5 hd6_le1

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
    let z := run6From w baseCaseSeed
    m ≤ z ∧ z ≤ m + 1 := by
  simp only
  let s : Nat := 22141993662453218394297550
  let m := icbrt w
  have hmlo : m * m * m ≤ w := icbrt_cube_le w
  have hmhi : w < (m + 1) * (m + 1) * (m + 1) := icbrt_lt_succ_cube w
  have hw_pos : 0 < w := by omega
  have hs_lo : 2 ^ 83 ≤ s := by
    change 2 ^ 83 ≤ baseCaseSeed
    exact baseCaseSeed_bounds.1
  have hsPos : 0 < s := by omega
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
  have hmz' : m ≤ run6From w baseCaseSeed := by
    simpa [s, baseCaseSeed] using hmz
  refine ⟨hmz', ?_⟩
  -- Case split on octave
  by_cases h252 : w < 2 ^ 252
  · -- Octave 251: w ∈ [2^251, 2^252)
    have hlo := lo_le_icbrt_of_cube_le_pow w octave251Lo 251 octave251_bounds.1 hw_lo
    have hhi := icbrt_le_hi_of_pow_lt_cube w octave251Hi 251 octave251_bounds.2 h252
    obtain ⟨h2d1, h2d2, h2d3, h2d4, h2d5, hd6_le1⟩ := octave251_chain_bounds
    simpa [s, baseCaseSeed] using octave_upper w m s octave251Lo octave251Hi octave251Gap octave251D1
      hsPos hmlo hmhi hlo hhi (Nat.le_trans octave251_lo_two_le hlo)
      (Nat.lt_of_lt_of_le (by omega : 0 < 2) octave251_lo_two_le)
      (by simpa [s, baseCaseSeed] using octave251_gap_eq)
      (by simpa [s, baseCaseSeed] using octave251_d1_formula_eq)
      h2d1 h2d2 h2d3 h2d4 h2d5 hd6_le1
  · by_cases h253 : w < 2 ^ 253
    · -- Octave 252: w ∈ [2^252, 2^253)
      have hlo := lo_le_icbrt_of_cube_le_pow w octave252Lo 252 octave252_bounds.1 (by omega)
      have hhi := icbrt_le_hi_of_pow_lt_cube w octave252Hi 252 octave252_bounds.2 h253
      obtain ⟨h2d1, h2d2, h2d3, h2d4, h2d5, hd6_le1⟩ := octave252_chain_bounds
      simpa [s, baseCaseSeed] using octave_upper w m s octave252Lo octave252Hi octave252Gap octave252D1
        hsPos hmlo hmhi hlo hhi (Nat.le_trans octave252_lo_two_le hlo)
        (Nat.lt_of_lt_of_le (by omega : 0 < 2) octave252_lo_two_le)
        (by simpa [s, baseCaseSeed] using octave252_gap_eq)
        (by simpa [s, baseCaseSeed] using octave252_d1_formula_eq)
        h2d1 h2d2 h2d3 h2d4 h2d5 hd6_le1
    · -- Octave 253: w ∈ [2^253, 2^254)
      have hlo := lo_le_icbrt_of_cube_le_pow w octave253Lo 253 octave253_lo_cube_le_pow253 (by omega)
      have hhi := icbrt_le_hi_of_pow_lt_cube w M_TOP 253 m_top_cube_bounds.2 hw_hi
      obtain ⟨h2d1, h2d2, h2d3, h2d4, h2d5, hd6_le1⟩ := octave253_chain_bounds
      simpa [s, baseCaseSeed] using octave_upper w m s octave253Lo M_TOP octave253Gap octave253D1
        hsPos hmlo hmhi hlo hhi (Nat.le_trans octave253_lo_two_le hlo)
        (Nat.lt_of_lt_of_le (by omega : 0 < 2) octave253_lo_two_le)
        (by simpa [s, baseCaseSeed] using octave253_gap_eq)
        (by simpa [s, baseCaseSeed] using octave253_d1_formula_eq)
        h2d1 h2d2 h2d3 h2d4 h2d5 hd6_le1

/-- 2 ≤ m follows from 2^83 ≤ m (omega can't handle this power directly). -/
theorem two_le_of_pow83_le (m : Nat) (h : 2 ^ 83 ≤ m) : 2 ≤ m :=
  Nat.le_trans (show 2 ≤ 2 ^ 83 from by
    rw [show (2 : Nat) ^ 83 = 2 * 2 ^ 82 from by
      rw [show (83 : Nat) = 1 + 82 from rfl, Nat.pow_add]]; omega) h

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
    lo_le_icbrt_of_cube_le_pow w (2 ^ 83) 251 pow83_cube_le_pow251 hw_lo
  have hm_hi : m < 2 ^ 85 := by
    show icbrt w < 2 ^ 85
    have := icbrt_le_hi_of_pow_lt_cube w (2 ^ 85 - 1) 253 pow254_le_succ_pow85_sub_one_cube hw_hi
    omega
  have hm_wm : m < WORD_MOD := by unfold WORD_MOD; omega
  have hm2_le : m * m ≤ (2 ^ 85 - 1) * (2 ^ 85 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hm2_wm : m * m < WORD_MOD := by
    have : (2 ^ 85 - 1) * (2 ^ 85 - 1) < WORD_MOD := pow85_sub_one_sq_lt_word
    omega
  have hm3_le : m * m * m ≤ (2 ^ 85 - 1) * (2 ^ 85 - 1) * (2 ^ 85 - 1) :=
    Nat.mul_le_mul hm2_le (by omega)
  have hm3_wm : m * m * m < WORD_MOD := by
    have : (2 ^ 85 - 1) * (2 ^ 85 - 1) * (2 ^ 85 - 1) < WORD_MOD := pow85_sub_one_cube_lt_word
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
  have hs_lo : 2 ^ 83 ≤ s := by
    change 2 ^ 83 ≤ baseCaseSeed
    exact baseCaseSeed_bounds.1
  have hs_hi : s < 2 ^ 88 := by
    change baseCaseSeed < 2 ^ 88
    exact baseCaseSeed_bounds.2
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
    have : evmAnd (evmAnd 2 255) 255 = 2 := baseCaseShiftMask_eq_two
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

-- ============================================================================
-- Bundled base case bounds (eliminates repeated extraction boilerplate)
-- ============================================================================

/-- All commonly needed bounds from the base case, bundled for easy destructuring.
    Callers can `obtain ⟨hm_lo, hm_hi, ...⟩ := baseCase_bounds ...` instead of
    extracting 10+ fields from model_cbrtBaseCase_evm_correct one by one. -/
theorem baseCase_bounds (x_hi_1 x_lo_1 : Nat)
    (hxhi_lo : 2 ^ 253 ≤ x_hi_1) (hxhi_hi : x_hi_1 < WORD_MOD)
    (hxlo : x_lo_1 < WORD_MOD) :
    let m := icbrt (x_hi_1 / 4)
    let R := m * 2 ^ 86
    let d := 3 * (m * m)
    let limb_hi := (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172
    let r_lo := ((x_hi_1 / 4 - m * m * m) * 2 ^ 86 + limb_hi) / d
    -- m bounds
    2 ^ 83 ≤ m ∧ m < 2 ^ 85 ∧ 2 ≤ m ∧ m < WORD_MOD ∧
    -- cube / residue
    m * m * m ≤ x_hi_1 / 4 ∧
    x_hi_1 / 4 - m * m * m ≤ 3 * (m * m) + 3 * m ∧
    -- d bounds
    0 < d ∧ d < WORD_MOD ∧
    -- R bounds
    2 ^ 169 ≤ R ∧ R < 2 ^ 171 ∧ 0 < R ∧
    -- limb / r_lo bounds
    limb_hi < 2 ^ 86 ∧ r_lo < 2 ^ 87 := by
  simp only
  have hbc := model_cbrtBaseCase_evm_correct x_hi_1 hxhi_lo hxhi_hi
  simp only at hbc
  let m := icbrt (x_hi_1 / 4)
  have hm_lo : 2 ^ 83 ≤ m := hbc.2.2.2.1
  have hm_hi : m < 2 ^ 85 := hbc.2.2.2.2.1
  have hm_pos : 2 ≤ m := two_le_of_pow83_le m hm_lo
  have hm_wm : m < WORD_MOD := hbc.2.2.2.2.2.2.2.1
  have hcube_le : m * m * m ≤ x_hi_1 / 4 := hbc.2.2.2.2.2.1
  have hres_bound := hbc.2.2.2.2.2.2.1
  have hd_pos : 0 < 3 * (m * m) := hbc.2.2.2.2.2.2.2.2.2.2
  have hd_wm : 3 * (m * m) < WORD_MOD := hbc.2.2.2.2.2.2.2.2.2.1
  -- R bounds
  have hR_lo : 2 ^ 169 ≤ m * 2 ^ 86 :=
    calc 2 ^ 169 = 2 ^ 83 * 2 ^ 86 := by rw [← Nat.pow_add]
      _ ≤ m * 2 ^ 86 := Nat.mul_le_mul_right _ hm_lo
  have hR_hi : m * 2 ^ 86 < 2 ^ 171 :=
    calc m * 2 ^ 86
        < 2 ^ 85 * 2 ^ 86 := Nat.mul_lt_mul_of_pos_right hm_hi (Nat.two_pow_pos 86)
      _ = 2 ^ 171 := by rw [← Nat.pow_add]
  -- limb_hi < 2^86
  have hlimb : (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172 < 2 ^ 86 := by
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
  -- r_lo < 2^87
  have hr_lo_bound : ((x_hi_1 / 4 - m * m * m) * 2 ^ 86 +
      ((x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172)) / (3 * (m * m)) < 2 ^ 87 := by
    rw [Nat.div_lt_iff_lt_mul hd_pos]
    have h2m : 2 * m ≤ m * m := Nat.mul_le_mul_right m (by omega)
    calc ((x_hi_1 / 4 - m * m * m) * 2 ^ 86 +
            ((x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172))
        < ((x_hi_1 / 4 - m * m * m) + 1) * 2 ^ 86 := by omega
      _ ≤ (3 * (m * m) + 3 * m + 1) * 2 ^ 86 := by
          apply Nat.mul_le_mul_right; exact Nat.succ_le_succ hres_bound
      _ ≤ (2 * (3 * (m * m))) * 2 ^ 86 := by
          apply Nat.mul_le_mul_right
          have h2m : 2 * m ≤ m * m := Nat.mul_le_mul_right m (by omega)
          omega
      _ = 2 ^ 87 * (3 * (m * m)) := by
          rw [show (2 : Nat) ^ 87 = 2 * 2 ^ 86 from by
            rw [show (87 : Nat) = 1 + 86 from rfl, Nat.pow_add]]; omega
  exact ⟨hm_lo, hm_hi, hm_pos, hm_wm, hcube_le, hres_bound,
         hd_pos, hd_wm, hR_lo, hR_hi, Nat.lt_of_lt_of_le (by omega : 0 < 2 ^ 169) hR_lo,
         hlimb, hr_lo_bound⟩

-- ============================================================================
-- Extended bounds: parametrized over abstract m, nat_r_lo, nat_rem
-- ============================================================================

/-- Extended bounds for CbrtComposition callers that parametrize over
    `(m : Nat) (hm_eq : m = icbrt (x_hi_1 / 4))` and separate quotient/remainder.
    Bundles all facts from `baseCase_bounds` plus `hr_lo_wm`, `hmm_hi`, `hrem_wm`. -/
theorem extended_bounds (x_hi_1 x_lo_1 : Nat)
    (hxhi_lo : 2 ^ 253 ≤ x_hi_1) (hxhi_hi : x_hi_1 < WORD_MOD)
    (hxlo : x_lo_1 < WORD_MOD)
    (m : Nat) (hm_eq : m = icbrt (x_hi_1 / 4))
    (nat_r_lo : Nat) (hr_lo_eq : nat_r_lo = ((x_hi_1 / 4 - m * m * m) * 2 ^ 86 +
        (x_hi_1 % 4 * 2 ^ 84 + x_lo_1 / 2 ^ 172)) / (3 * (m * m)))
    (nat_rem : Nat) (hrem_eq : nat_rem = ((x_hi_1 / 4 - m * m * m) * 2 ^ 86 +
        (x_hi_1 % 4 * 2 ^ 84 + x_lo_1 / 2 ^ 172)) % (3 * (m * m))) :
    -- m bounds
    2 ^ 83 ≤ m ∧ m < 2 ^ 85 ∧ 2 ≤ m ∧ m < WORD_MOD ∧
    -- cube / residue
    m * m * m ≤ x_hi_1 / 4 ∧
    x_hi_1 / 4 - m * m * m ≤ 3 * (m * m) + 3 * m ∧
    -- d bounds
    0 < 3 * (m * m) ∧ 3 * (m * m) < WORD_MOD ∧
    -- R bounds
    2 ^ 169 ≤ m * 2 ^ 86 ∧ m * 2 ^ 86 < 2 ^ 171 ∧ 0 < m * 2 ^ 86 ∧
    -- limb / r_lo / r_lo_wm
    (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172 < 2 ^ 86 ∧
    nat_r_lo < 2 ^ 87 ∧ nat_r_lo < WORD_MOD ∧
    -- mm / rem
    m * m < 2 ^ 170 ∧ nat_rem < WORD_MOD := by
  subst hm_eq
  have hb := baseCase_bounds x_hi_1 x_lo_1 hxhi_lo hxhi_hi hxlo
  simp only at hb ⊢
  obtain ⟨hm_lo, hm_hi, hm_pos, hm_wm, hcube_le, hres_bound,
          hd_pos, hd_wm, hR_lo, hR_hi, hR_pos, hlimb, hr_lo_bound⟩ := hb
  have hr_lo_bound' : nat_r_lo < 2 ^ 87 := by rw [hr_lo_eq]; exact hr_lo_bound
  have hr_lo_wm : nat_r_lo < WORD_MOD := by unfold WORD_MOD; omega
  have hmm_hi : icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4) < 2 ^ 170 :=
    calc icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)
        < icbrt (x_hi_1 / 4) * 2 ^ 85 :=
          Nat.mul_lt_mul_of_pos_left hm_hi (by omega)
      _ ≤ 2 ^ 85 * 2 ^ 85 := Nat.mul_le_mul_right _ (Nat.le_of_lt hm_hi)
      _ = 2 ^ 170 := by rw [← Nat.pow_add]
  have hrem_wm : nat_rem < WORD_MOD := by
    rw [hrem_eq]; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hd_pos) (Nat.le_of_lt hd_wm)
  exact ⟨hm_lo, hm_hi, hm_pos, hm_wm, hcube_le, hres_bound,
         hd_pos, hd_wm, hR_lo, hR_hi, hR_pos, hlimb, hr_lo_bound', hr_lo_wm,
         hmm_hi, hrem_wm⟩

end Cbrt512Spec

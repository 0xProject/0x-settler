import Cbrt512Proof.GeneratedCbrt512Model
import CbrtProof.FiniteCert

/- Literal-heavy numeric certificates for the 512-bit cube-root proof. -/

namespace Cbrt512Spec

open Cbrt512GeneratedModel
open CbrtCert

-- ============================================================================
-- Shared constants
-- ============================================================================

def baseCaseSeed : Nat := 22141993662453218394297550

def octave251Lo : Nat := 15352400942462240883748044
def octave251Hi : Nat := 19342813113834066795298815
def octave251Gap : Nat := 6789592719990977510549506
def octave251D1 : Nat := 1994218922075376856504634

def octave252Lo : Nat := 19342813113834066795298816
def octave252Hi : Nat := 24370417406302138235346347
def octave252Gap : Nat := 2799180548619151598998734
def octave252D1 : Nat := 365742585066387069963242

def M_TOP : Nat := 0x1965fea53d6e3c82b05999
def octave253Lo : Nat := 24370417406302138235346347
def octave253Gap : Nat := 8562808222471263373198539
def octave253D1 : Nat := 3738299367780524623633435

def R_MAX : Nat := 0x6597fa94f5b8f20ac16666ad0f7137bc6601d885628

-- ============================================================================
-- Base-case certificates
-- ============================================================================

set_option exponentiation.threshold 1024 in
theorem baseCaseSeed_bounds :
    2 ^ 83 ≤ baseCaseSeed ∧ baseCaseSeed < 2 ^ 88 := by
  unfold baseCaseSeed
  decide

set_option exponentiation.threshold 1024 in
theorem pow83_cube_le_pow251 :
    (2 ^ 83) * (2 ^ 83) * (2 ^ 83) ≤ 2 ^ 251 := by
  decide

set_option exponentiation.threshold 1024 in
theorem pow254_le_succ_pow85_sub_one_cube :
    2 ^ 254 ≤ ((2 ^ 85 - 1) + 1) * ((2 ^ 85 - 1) + 1) * ((2 ^ 85 - 1) + 1) := by
  decide

set_option exponentiation.threshold 1024 in
theorem pow85_sub_one_sq_lt_word :
    (2 ^ 85 - 1) * (2 ^ 85 - 1) < WORD_MOD := by
  unfold WORD_MOD
  decide

set_option exponentiation.threshold 1024 in
theorem pow85_sub_one_cube_lt_word :
    (2 ^ 85 - 1) * (2 ^ 85 - 1) * (2 ^ 85 - 1) < WORD_MOD := by
  unfold WORD_MOD
  decide

set_option exponentiation.threshold 1024 in
theorem octave251_bounds :
    octave251Lo * octave251Lo * octave251Lo ≤ 2 ^ 251 ∧
    2 ^ 252 ≤ (octave251Hi + 1) * (octave251Hi + 1) * (octave251Hi + 1) := by
  unfold octave251Lo octave251Hi
  decide

set_option exponentiation.threshold 1024 in
theorem octave251_lo_two_le : 2 ≤ octave251Lo := by
  unfold octave251Lo
  decide

set_option exponentiation.threshold 1024 in
theorem octave252_bounds :
    octave252Lo * octave252Lo * octave252Lo ≤ 2 ^ 252 ∧
    2 ^ 253 ≤ (octave252Hi + 1) * (octave252Hi + 1) * (octave252Hi + 1) := by
  unfold octave252Lo octave252Hi
  decide

set_option exponentiation.threshold 1024 in
theorem octave252_lo_two_le : 2 ≤ octave252Lo := by
  unfold octave252Lo
  decide

set_option exponentiation.threshold 1024 in
theorem octave253_lo_cube_le_pow253 :
    octave253Lo * octave253Lo * octave253Lo ≤ 2 ^ 253 := by
  unfold octave253Lo
  decide

set_option exponentiation.threshold 1024 in
theorem octave253_lo_two_le : 2 ≤ octave253Lo := by
  unfold octave253Lo
  decide

set_option exponentiation.threshold 1024 in
theorem octave251_gap_eq :
    max (baseCaseSeed - octave251Lo) (octave251Hi - baseCaseSeed) = octave251Gap := by
  unfold baseCaseSeed octave251Lo octave251Hi octave251Gap
  decide

set_option exponentiation.threshold 1024 in
theorem octave252_gap_eq :
    max (baseCaseSeed - octave252Lo) (octave252Hi - baseCaseSeed) = octave252Gap := by
  unfold baseCaseSeed octave252Lo octave252Hi octave252Gap
  decide

set_option exponentiation.threshold 1024 in
theorem octave253_gap_eq :
    max (baseCaseSeed - octave253Lo) (M_TOP - baseCaseSeed) = octave253Gap := by
  unfold baseCaseSeed octave253Lo M_TOP octave253Gap
  decide

set_option exponentiation.threshold 1024 in
theorem octave251_d1_formula_eq :
    (octave251Gap * octave251Gap * (octave251Hi + 2 * baseCaseSeed) +
      3 * octave251Hi * (octave251Hi + 1)) / (3 * (baseCaseSeed * baseCaseSeed)) =
      octave251D1 := by
  unfold octave251Gap octave251Hi baseCaseSeed octave251D1
  decide

set_option exponentiation.threshold 1024 in
theorem octave252_d1_formula_eq :
    (octave252Gap * octave252Gap * (octave252Hi + 2 * baseCaseSeed) +
      3 * octave252Hi * (octave252Hi + 1)) / (3 * (baseCaseSeed * baseCaseSeed)) =
      octave252D1 := by
  unfold octave252Gap octave252Hi baseCaseSeed octave252D1
  decide

set_option exponentiation.threshold 1024 in
theorem octave253_d1_formula_eq :
    (octave253Gap * octave253Gap * (M_TOP + 2 * baseCaseSeed) +
      3 * M_TOP * (M_TOP + 1)) / (3 * (baseCaseSeed * baseCaseSeed)) =
      octave253D1 := by
  unfold octave253Gap M_TOP baseCaseSeed octave253D1
  decide

set_option exponentiation.threshold 1024 in
theorem octave251_chain_bounds :
    2 * octave251D1 ≤ octave251Lo ∧
    2 * nextD octave251Lo octave251D1 ≤ octave251Lo ∧
    2 * nextD octave251Lo (nextD octave251Lo octave251D1) ≤ octave251Lo ∧
    2 * nextD octave251Lo (nextD octave251Lo (nextD octave251Lo octave251D1)) ≤ octave251Lo ∧
    2 * nextD octave251Lo
      (nextD octave251Lo (nextD octave251Lo (nextD octave251Lo octave251D1))) ≤ octave251Lo ∧
    nextD octave251Lo
      (nextD octave251Lo
        (nextD octave251Lo
          (nextD octave251Lo (nextD octave251Lo octave251D1)))) ≤ 1 := by
  unfold octave251D1 octave251Lo nextD
  decide

set_option exponentiation.threshold 1024 in
theorem octave252_chain_bounds :
    2 * octave252D1 ≤ octave252Lo ∧
    2 * nextD octave252Lo octave252D1 ≤ octave252Lo ∧
    2 * nextD octave252Lo (nextD octave252Lo octave252D1) ≤ octave252Lo ∧
    2 * nextD octave252Lo (nextD octave252Lo (nextD octave252Lo octave252D1)) ≤ octave252Lo ∧
    2 * nextD octave252Lo
      (nextD octave252Lo (nextD octave252Lo (nextD octave252Lo octave252D1))) ≤ octave252Lo ∧
    nextD octave252Lo
      (nextD octave252Lo
        (nextD octave252Lo
          (nextD octave252Lo (nextD octave252Lo octave252D1)))) ≤ 1 := by
  unfold octave252D1 octave252Lo nextD
  decide

set_option exponentiation.threshold 1024 in
theorem octave253_chain_bounds :
    2 * octave253D1 ≤ octave253Lo ∧
    2 * nextD octave253Lo octave253D1 ≤ octave253Lo ∧
    2 * nextD octave253Lo (nextD octave253Lo octave253D1) ≤ octave253Lo ∧
    2 * nextD octave253Lo (nextD octave253Lo (nextD octave253Lo octave253D1)) ≤ octave253Lo ∧
    2 * nextD octave253Lo
      (nextD octave253Lo (nextD octave253Lo (nextD octave253Lo octave253D1))) ≤ octave253Lo ∧
    nextD octave253Lo
      (nextD octave253Lo
        (nextD octave253Lo
          (nextD octave253Lo (nextD octave253Lo octave253D1)))) ≤ 1 := by
  unfold octave253D1 octave253Lo nextD
  decide

set_option exponentiation.threshold 1024 in
theorem baseCaseShiftMask_eq_two : evmAnd (evmAnd 2 255) 255 = 2 := by
  unfold evmAnd u256 WORD_MOD
  decide

-- ============================================================================
-- QC certificates
-- ============================================================================

set_option exponentiation.threshold 1024 in
theorem mask_86_eq : 77371252455336267181195263 = 2 ^ 86 - 1 := by
  decide

-- ============================================================================
-- Range certificates
-- ============================================================================

set_option exponentiation.threshold 1024 in
theorem r_max_cube_lt_wm2 : R_MAX * R_MAX * R_MAX < WORD_MOD * WORD_MOD := by
  unfold R_MAX WORD_MOD
  decide

set_option exponentiation.threshold 1024 in
theorem r_max_is_icbrt_wm2 :
    R_MAX * R_MAX * R_MAX ≤ WORD_MOD * WORD_MOD - 1 ∧
    WORD_MOD * WORD_MOD - 1 < (R_MAX + 1) * (R_MAX + 1) * (R_MAX + 1) := by
  unfold R_MAX WORD_MOD
  constructor <;> decide

set_option exponentiation.threshold 1024 in
theorem m_top_cube_bounds :
    M_TOP * M_TOP * M_TOP ≤ 2 ^ 254 - 1 ∧
    2 ^ 254 ≤ (M_TOP + 1) * (M_TOP + 1) * (M_TOP + 1) := by
  unfold M_TOP
  constructor <;> decide

set_option exponentiation.threshold 1024 in
theorem r_max_ge_r_top : M_TOP * 2 ^ 86 ≤ R_MAX := by
  unfold M_TOP R_MAX
  decide

set_option exponentiation.threshold 1024 in
theorem r_lo_max_at_m_top :
    let R := M_TOP * 2 ^ 86
    let delta := R_MAX - R
    let res_max := 2 ^ 254 - 1 - M_TOP * M_TOP * M_TOP
    let d := 3 * (M_TOP * M_TOP)
    (res_max * 2 ^ 86 + 2 ^ 86 - 1) / d ≤ delta + 1 ∧
    (delta + 1) * (delta + 1) / R ≥ 1 ∧
    9 ≤ delta := by
  unfold M_TOP R_MAX
  decide

set_option exponentiation.threshold 1024 in
theorem m_top_three_msq_plus_3m_lt_pow171 :
    3 * (M_TOP * M_TOP) + 3 * M_TOP < 2 ^ 171 := by
  unfold M_TOP
  decide

end Cbrt512Spec

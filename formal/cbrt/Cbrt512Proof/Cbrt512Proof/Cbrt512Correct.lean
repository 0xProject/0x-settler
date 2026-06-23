/-
  Ceiling cube root for 512-bit values.
-/
import Mathlib.Tactic.Ring
import FormalYul.Preservation
import CbrtProof.CbrtCorrect
import CbrtProof.CertifiedChain
import CbrtProof.FiniteCert

open FormalYul
open CbrtCertified
open CbrtCert

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
    2 ^ 254 ≤ ((2 ^ 85 - 1) + 1) * ((2 ^ 85 - 1) + 1) *
      ((2 ^ 85 - 1) + 1) := by
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
    max (baseCaseSeed - octave251Lo) (octave251Hi - baseCaseSeed) =
      octave251Gap := by
  unfold baseCaseSeed octave251Lo octave251Hi octave251Gap
  decide

set_option exponentiation.threshold 1024 in
theorem octave252_gap_eq :
    max (baseCaseSeed - octave252Lo) (octave252Hi - baseCaseSeed) =
      octave252Gap := by
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
      3 * octave251Hi * (octave251Hi + 1)) /
        (3 * (baseCaseSeed * baseCaseSeed)) = octave251D1 := by
  unfold octave251Gap octave251Hi baseCaseSeed octave251D1
  decide

set_option exponentiation.threshold 1024 in
theorem octave252_d1_formula_eq :
    (octave252Gap * octave252Gap * (octave252Hi + 2 * baseCaseSeed) +
      3 * octave252Hi * (octave252Hi + 1)) /
        (3 * (baseCaseSeed * baseCaseSeed)) = octave252D1 := by
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
    2 * nextD octave251Lo (nextD octave251Lo (nextD octave251Lo octave251D1)) ≤
      octave251Lo ∧
    2 * nextD octave251Lo
      (nextD octave251Lo (nextD octave251Lo (nextD octave251Lo octave251D1))) ≤
        octave251Lo ∧
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
    2 * nextD octave252Lo (nextD octave252Lo (nextD octave252Lo octave252D1)) ≤
      octave252Lo ∧
    2 * nextD octave252Lo
      (nextD octave252Lo (nextD octave252Lo (nextD octave252Lo octave252D1))) ≤
        octave252Lo ∧
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
    2 * nextD octave253Lo (nextD octave253Lo (nextD octave253Lo octave253D1)) ≤
      octave253Lo ∧
    2 * nextD octave253Lo
      (nextD octave253Lo (nextD octave253Lo (nextD octave253Lo octave253D1))) ≤
        octave253Lo ∧
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

set_option exponentiation.threshold 1024 in
theorem mask_86_eq : 77371252455336267181195263 = 2 ^ 86 - 1 := by
  decide

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

theorem cbrt512_evmClz_of_pos (xHi : Nat)
    (hpos : 0 < xHi) (hlt : xHi < WORD_MOD) :
    evmClz xHi = 255 - Nat.log2 xHi := by
  rw [FormalYul.Preservation.evmClz_eq_of_lt xHi hlt]
  simp [Nat.ne_of_gt hpos]

theorem cbrt512_shift_lt_86 (xHi : Nat)
    (hpos : 0 < xHi) (hlt : xHi < WORD_MOD) :
    evmClz xHi / 3 < 86 := by
  have hclz : evmClz xHi < 256 := by
    rw [cbrt512_evmClz_of_pos xHi hpos hlt]
    have hlog : Nat.log2 xHi < 256 :=
      (Nat.log2_lt (Nat.ne_of_gt hpos)).2 (by
        unfold WORD_MOD at hlt
        exact hlt)
    omega
  omega

theorem cbrt512_three_shift_lt_256 (xHi : Nat)
    (hpos : 0 < xHi) (hlt : xHi < WORD_MOD) :
    3 * (evmClz xHi / 3) < 256 := by
  have h := cbrt512_shift_lt_86 xHi hpos hlt
  omega

set_option exponentiation.threshold 1024 in
theorem cbrt512_norm_no_overflow (xHi xLo : Nat)
    (hxHiPos : 0 < xHi) (hxHi : xHi < WORD_MOD) (hxLo : xLo < WORD_MOD) :
    (xHi * WORD_MOD + xLo) * 2 ^ (3 * (evmClz xHi / 3)) <
      WORD_MOD * WORD_MOD := by
  have hne : xHi ≠ 0 := Nat.ne_of_gt hxHiPos
  have hHiLog : xHi < 2 ^ (Nat.log2 xHi + 1) :=
    (Nat.log2_lt hne).mp (by omega)
  have hLogLe : Nat.log2 xHi ≤ 255 := by
    exact Nat.lt_succ_iff.mp ((Nat.log2_lt hne).2 (by
      unfold WORD_MOD at hxHi
      exact hxHi))
  have hLogShift : Nat.log2 xHi + 1 + 3 * (evmClz xHi / 3) ≤ 256 := by
    rw [cbrt512_evmClz_of_pos xHi hxHiPos hxHi]
    have hdiv := Nat.div_add_mod (255 - Nat.log2 xHi) 3
    have hmod := Nat.mod_lt (255 - Nat.log2 xHi) (by omega : 0 < 3)
    omega
  have hxLt : xHi * WORD_MOD + xLo < 2 ^ (Nat.log2 xHi + 1 + 256) := by
    calc xHi * WORD_MOD + xLo
        < xHi * WORD_MOD + WORD_MOD := by omega
      _ = (xHi + 1) * WORD_MOD := by rw [Nat.succ_mul]
      _ ≤ 2 ^ (Nat.log2 xHi + 1) * WORD_MOD :=
          Nat.mul_le_mul_right _ hHiLog
      _ = 2 ^ (Nat.log2 xHi + 1 + 256) := by
        unfold WORD_MOD
        exact (Nat.pow_add 2 _ 256).symm
  calc (xHi * WORD_MOD + xLo) * 2 ^ (3 * (evmClz xHi / 3))
      < 2 ^ (Nat.log2 xHi + 1 + 256) * 2 ^ (3 * (evmClz xHi / 3)) :=
        Nat.mul_lt_mul_of_pos_right hxLt (Nat.two_pow_pos _)
    _ = 2 ^ (Nat.log2 xHi + 1 + 256 + 3 * (evmClz xHi / 3)) :=
        (Nat.pow_add 2 _ _).symm
    _ ≤ WORD_MOD * WORD_MOD := by
      unfold WORD_MOD
      rw [← Nat.pow_add]
      exact Nat.pow_le_pow_right (by omega) (by omega)

theorem cbrt512_normalized_hi_ge_253 (xHi xLo : Nat)
    (hxHiPos : 0 < xHi) (hxHi : xHi < WORD_MOD) (hxLo : xLo < WORD_MOD) :
    let shift := evmClz xHi / 3
    let s3 := 3 * shift
    let shiftedHi := (xHi * 2 ^ s3 + xLo * 2 ^ s3 / WORD_MOD) % WORD_MOD
    2 ^ 253 ≤ shiftedHi := by
  simp only
  have hne : xHi ≠ 0 := Nat.ne_of_gt hxHiPos
  rw [cbrt512_evmClz_of_pos xHi hxHiPos hxHi]
  generalize hLDef : Nat.log2 xHi = L
  generalize hs3Def : 3 * ((255 - L) / 3) = s3
  have hLLt : L < 256 := by
    rw [← hLDef]
    exact (Nat.log2_lt hne).2 (by
      unfold WORD_MOD at hxHi
      exact hxHi)
  have hLLo : 2 ^ L ≤ xHi := by
    suffices ¬ xHi < 2 ^ L by omega
    intro hlt
    have := (Nat.log2_lt hne).mpr hlt
    omega
  have hLHi : xHi < 2 ^ (L + 1) := by
    have : Nat.log2 xHi < L + 1 := by omega
    exact (Nat.log2_lt hne).mp this
  have hDiv := Nat.div_add_mod (255 - L) 3
  have hMod := Nat.mod_lt (255 - L) (by omega : 0 < 3)
  have hLs3 : 253 ≤ L + s3 := by omega
  have hProdLo : 2 ^ 253 ≤ xHi * 2 ^ s3 :=
    calc 2 ^ 253 ≤ 2 ^ (L + s3) := Nat.pow_le_pow_right (by omega) hLs3
      _ = 2 ^ L * 2 ^ s3 := Nat.pow_add 2 L s3
      _ ≤ xHi * 2 ^ s3 := Nat.mul_le_mul_right _ hLLo
  have hDivBound : xLo * 2 ^ s3 / WORD_MOD < 2 ^ s3 := by
    rw [Nat.div_lt_iff_lt_mul (by unfold WORD_MOD; exact Nat.two_pow_pos 256)]
    calc xLo * 2 ^ s3
        < WORD_MOD * 2 ^ s3 := Nat.mul_lt_mul_of_pos_right hxLo (Nat.two_pow_pos s3)
      _ = 2 ^ s3 * WORD_MOD := Nat.mul_comm _ _
  have hsumLt : xHi * 2 ^ s3 + xLo * 2 ^ s3 / WORD_MOD < WORD_MOD := by
    have hLs3Up : L + 1 + s3 ≤ 256 := by omega
    calc xHi * 2 ^ s3 + xLo * 2 ^ s3 / WORD_MOD
        < xHi * 2 ^ s3 + 2 ^ s3 := by omega
      _ = (xHi + 1) * 2 ^ s3 := (Nat.succ_mul xHi (2 ^ s3)).symm
      _ ≤ 2 ^ (L + 1) * 2 ^ s3 := Nat.mul_le_mul_right _ hLHi
      _ = 2 ^ (L + 1 + s3) := (Nat.pow_add 2 (L + 1) s3).symm
      _ ≤ WORD_MOD := by
        unfold WORD_MOD
        exact Nat.pow_le_pow_right (by omega) hLs3Up
  rw [Nat.mod_eq_of_lt hsumLt]
  exact Nat.le_trans hProdLo (Nat.le_add_right _ _)

private theorem cbrt512_shl512_hi (xHi xLo s : Nat) (hs : s ≤ 255) :
    (xHi * WORD_MOD + xLo) * 2 ^ s / WORD_MOD =
      xHi * 2 ^ s + xLo / 2 ^ (256 - s) := by
  have hrw : (xHi * WORD_MOD + xLo) * 2 ^ s =
      xLo * 2 ^ s + xHi * 2 ^ s * WORD_MOD := by
    rw [Nat.add_mul, Nat.mul_right_comm]
    omega
  rw [hrw, Nat.add_mul_div_right _ _ (by unfold WORD_MOD; exact Nat.two_pow_pos 256),
    Nat.add_comm]
  congr 1
  rw [show WORD_MOD = 2 ^ (256 - s) * 2 ^ s from by
    unfold WORD_MOD
    rw [← Nat.pow_add]
    congr 1
    omega]
  exact Nat.mul_div_mul_right _ _ (Nat.two_pow_pos s)

private theorem cbrt512_shl512_lo (xHi xLo s : Nat) :
    (xHi * WORD_MOD + xLo) * 2 ^ s % WORD_MOD =
      (xLo * 2 ^ s) % WORD_MOD := by
  have hrw : (xHi * WORD_MOD + xLo) * 2 ^ s =
      xLo * 2 ^ s + xHi * 2 ^ s * WORD_MOD := by
    rw [Nat.add_mul, Nat.mul_right_comm]
    omega
  rw [hrw, Nat.add_mul_mod_self_right]

private theorem cbrt512_or_eq_add_shl (a b s : Nat) (hb : b < 2 ^ s) :
    (a * 2 ^ s) ||| b = a * 2 ^ s + b := by
  rw [← Nat.shiftLeft_eq]
  exact (Nat.shiftLeft_add_eq_or_of_lt hb a).symm

private theorem cbrt512_shl_or_shr (xHi xLo s : Nat)
    (hsPos : 0 < s) (hs : s ≤ 255)
    (hxHiShl : xHi * 2 ^ s < WORD_MOD) (hxLo : xLo < WORD_MOD) :
    ((xHi * 2 ^ s) % WORD_MOD) ||| (xLo / 2 ^ (256 - s)) =
      (xHi * WORD_MOD + xLo) * 2 ^ s / WORD_MOD := by
  rw [Nat.mod_eq_of_lt hxHiShl]
  have hcarry : xLo / 2 ^ (256 - s) < 2 ^ s := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    calc xLo < WORD_MOD := hxLo
      _ = 2 ^ s * 2 ^ (256 - s) := by
        unfold WORD_MOD
        rw [← Nat.pow_add]
        congr 1
        omega
  rw [cbrt512_or_eq_add_shl xHi (xLo / 2 ^ (256 - s)) s hcarry,
    cbrt512_shl512_hi xHi xLo s hs]

set_option exponentiation.threshold 1024 in
theorem cbrt512_evm_normalization_correct (xHi xLo : Nat)
    (hxHiPos : 0 < xHi) (hxHi : xHi < WORD_MOD) (hxLo : xLo < WORD_MOD) :
    let shift := evmDiv (evmClz xHi) 3
    let s3 := evmMul shift 3
    let shiftedLo := evmShl s3 xLo
    let shiftedHi := evmOr (evmShl s3 xHi) (evmShr (evmSub 256 s3) xLo)
    shift = evmClz xHi / 3 ∧
    s3 = 3 * shift ∧
    shiftedHi * WORD_MOD + shiftedLo =
      (xHi * WORD_MOD + xLo) * 2 ^ (3 * (evmClz xHi / 3)) %
        (WORD_MOD * WORD_MOD) ∧
    2 ^ 253 ≤ shiftedHi ∧
    shiftedHi < WORD_MOD ∧
    shiftedLo < WORD_MOD := by
  simp only
  have hclzW : evmClz xHi < WORD_MOD := FormalYul.Preservation.evmClz_lt_WORD_MOD xHi
  have h3W : (3 : Nat) < WORD_MOD := FormalYul.Preservation.three_lt_word
  have h256W : (256 : Nat) < WORD_MOD := FormalYul.Preservation.word_mod_gt_256
  have hshiftLt := cbrt512_shift_lt_86 xHi hxHiPos hxHi
  have hs3Lt := cbrt512_three_shift_lt_256 xHi hxHiPos hxHi
  let shift := evmClz xHi / 3
  let s3 := 3 * shift
  have hshiftW : shift < WORD_MOD := by unfold WORD_MOD; omega
  have hs3W : s3 < WORD_MOD := by unfold WORD_MOD; omega
  have hshiftEq : evmDiv (evmClz xHi) 3 = shift := by
    exact FormalYul.Preservation.evmDiv_eq_of_lt (evmClz xHi) 3 hclzW
      (by omega) h3W
  have hs3Eq : evmMul shift 3 = s3 := by
    rw [FormalYul.Preservation.evmMul_eq_mod_of_lt shift 3 hshiftW h3W]
    rw [Nat.mod_eq_of_lt (by unfold WORD_MOD; omega : shift * 3 < WORD_MOD)]
    omega
  rw [hshiftEq, hs3Eq]
  have hsubEq : evmSub 256 s3 = 256 - s3 :=
    FormalYul.Preservation.evmSub_eq_of_le 256 s3 h256W (by omega)
  have hshlHi : evmShl s3 xHi = (xHi * 2 ^ s3) % WORD_MOD := by
    exact FormalYul.Preservation.evmShl_eq_of_lt s3 xHi hs3Lt hxHi
  have hshlLo : evmShl s3 xLo = (xLo * 2 ^ s3) % WORD_MOD := by
    exact FormalYul.Preservation.evmShl_eq_of_lt s3 xLo hs3Lt hxLo
  have hne : xHi ≠ 0 := Nat.ne_of_gt hxHiPos
  have hHiLog : xHi < 2 ^ (Nat.log2 xHi + 1) :=
    (Nat.log2_lt hne).mp (by omega)
  have hLogLe : Nat.log2 xHi ≤ 255 := by
    exact Nat.lt_succ_iff.mp ((Nat.log2_lt hne).2 (by
      unfold WORD_MOD at hxHi
      exact hxHi))
  have hLogShiftUp : Nat.log2 xHi + 1 + s3 ≤ 256 := by
    show Nat.log2 xHi + 1 + 3 * (evmClz xHi / 3) ≤ 256
    rw [cbrt512_evmClz_of_pos xHi hxHiPos hxHi]
    have hdiv := Nat.div_add_mod (255 - Nat.log2 xHi) 3
    have hmod := Nat.mod_lt (255 - Nat.log2 xHi) (by omega : 0 < 3)
    omega
  have hHiShlLt : xHi * 2 ^ s3 < WORD_MOD :=
    calc xHi * 2 ^ s3
        < 2 ^ (Nat.log2 xHi + 1) * 2 ^ s3 :=
          Nat.mul_lt_mul_of_pos_right hHiLog (Nat.two_pow_pos s3)
      _ = 2 ^ (Nat.log2 xHi + 1 + s3) := (Nat.pow_add 2 _ s3).symm
      _ ≤ WORD_MOD := by
        unfold WORD_MOD
        exact Nat.pow_le_pow_right (by omega) hLogShiftUp
  by_cases hs3Zero : s3 = 0
  · have hshrEq : evmShr (evmSub 256 s3) xLo = 0 := by
      rw [hsubEq, hs3Zero]
      unfold evmShr u256
      simp [Nat.mod_eq_of_lt h256W]
    have hshlHi0 : evmShl s3 xHi = xHi := by
      rw [hshlHi, hs3Zero, Nat.pow_zero, Nat.mul_one]
      exact Nat.mod_eq_of_lt hxHi
    have hshlLo0 : evmShl s3 xLo = xLo := by
      rw [hshlLo, hs3Zero, Nat.pow_zero, Nat.mul_one]
      exact Nat.mod_eq_of_lt hxLo
    have hhiEq : evmOr (evmShl s3 xHi) (evmShr (evmSub 256 s3) xLo) = xHi := by
      have hshlW : evmShl s3 xHi < WORD_MOD := by rw [hshlHi0]; exact hxHi
      have hshrW : evmShr (evmSub 256 s3) xLo < WORD_MOD := by
        rw [hshrEq]
        exact FormalYul.Preservation.zero_lt_word
      rw [FormalYul.Preservation.evmOr_eq_of_lt _ _ hshlW hshrW,
        hshlHi0, hshrEq]
      simp
    have hrecon : xHi * WORD_MOD + xLo =
        (xHi * WORD_MOD + xLo) * 2 ^ s3 % (WORD_MOD * WORD_MOD) := by
      rw [hs3Zero, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt]
      calc xHi * WORD_MOD + xLo
          < xHi * WORD_MOD + WORD_MOD := by omega
        _ = (xHi + 1) * WORD_MOD := by rw [Nat.succ_mul]
        _ ≤ WORD_MOD * WORD_MOD := Nat.mul_le_mul_right _ hxHi
    have hge253 : 2 ^ 253 ≤ xHi := by
      have h := cbrt512_normalized_hi_ge_253 xHi xLo hxHiPos hxHi hxLo
      simp only at h
      rw [show 3 * (evmClz xHi / 3) = 0 from hs3Zero] at h
      rw [Nat.pow_zero, Nat.mul_one, Nat.mul_one,
        Nat.div_eq_of_lt hxLo, Nat.add_zero, Nat.mod_eq_of_lt hxHi] at h
      exact h
    refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
    · rw [hhiEq, hshlLo0]
      exact hrecon
    · rw [hhiEq]
      exact hge253
    · rw [hhiEq]
      exact hxHi
    · rw [hshlLo0]
      exact hxLo
  · have hs3Pos : 0 < s3 := by omega
    have hshrEq : evmShr (evmSub 256 s3) xLo = xLo / 2 ^ (256 - s3) := by
      rw [hsubEq]
      exact FormalYul.Preservation.evmShr_eq_of_lt (256 - s3) xLo (by omega) hxLo
    have hdivLt : xLo / 2 ^ (256 - s3) < 2 ^ s3 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
      calc xLo < WORD_MOD := hxLo
        _ = 2 ^ s3 * 2 ^ (256 - s3) := by
          unfold WORD_MOD
          rw [← Nat.pow_add]
          congr 1
          omega
    have hshlW : evmShl s3 xHi < WORD_MOD := by
      rw [hshlHi]
      exact Nat.mod_lt _ (by unfold WORD_MOD; exact Nat.two_pow_pos 256)
    have hshrW : evmShr (evmSub 256 s3) xLo < WORD_MOD := by
      rw [hshrEq]
      exact Nat.lt_of_lt_of_le hdivLt (by
        unfold WORD_MOD
        exact Nat.pow_le_pow_right (by omega) (by omega))
    have hhiEq : evmOr (evmShl s3 xHi) (evmShr (evmSub 256 s3) xLo) =
        (xHi * WORD_MOD + xLo) * 2 ^ s3 / WORD_MOD := by
      rw [FormalYul.Preservation.evmOr_eq_of_lt _ _ hshlW hshrW,
        hshlHi, hshrEq]
      exact cbrt512_shl_or_shr xHi xLo s3 hs3Pos (by omega) hHiShlLt hxLo
    have hloEq : evmShl s3 xLo =
        (xHi * WORD_MOD + xLo) * 2 ^ s3 % WORD_MOD := by
      rw [hshlLo]
      exact (cbrt512_shl512_lo xHi xLo s3).symm
    have hhiVal := cbrt512_shl512_hi xHi xLo s3 (by omega : s3 ≤ 255)
    have hhiLt : (xHi * WORD_MOD + xLo) * 2 ^ s3 / WORD_MOD < WORD_MOD := by
      rw [hhiVal]
      calc xHi * 2 ^ s3 + xLo / 2 ^ (256 - s3)
          < xHi * 2 ^ s3 + 2 ^ s3 := by omega
        _ = (xHi + 1) * 2 ^ s3 := (Nat.succ_mul xHi (2 ^ s3)).symm
        _ ≤ 2 ^ (Nat.log2 xHi + 1) * 2 ^ s3 :=
          Nat.mul_le_mul_right _ hHiLog
        _ = 2 ^ (Nat.log2 xHi + 1 + s3) := (Nat.pow_add 2 _ s3).symm
        _ ≤ WORD_MOD := by
          unfold WORD_MOD
          exact Nat.pow_le_pow_right (by omega) hLogShiftUp
    have hloLt : (xHi * WORD_MOD + xLo) * 2 ^ s3 % WORD_MOD < WORD_MOD :=
      Nat.mod_lt _ (by unfold WORD_MOD; exact Nat.two_pow_pos 256)
    have hprodLt :
        (xHi * WORD_MOD + xLo) * 2 ^ s3 < WORD_MOD * WORD_MOD := by
      have hdm := Nat.div_add_mod ((xHi * WORD_MOD + xLo) * 2 ^ s3) WORD_MOD
      rw [← hdm]
      calc WORD_MOD * ((xHi * WORD_MOD + xLo) * 2 ^ s3 / WORD_MOD) +
            (xHi * WORD_MOD + xLo) * 2 ^ s3 % WORD_MOD
          < WORD_MOD * (((xHi * WORD_MOD + xLo) * 2 ^ s3 / WORD_MOD) + 1) := by
            rw [Nat.mul_add, Nat.mul_one]
            exact Nat.add_lt_add_left hloLt _
        _ ≤ WORD_MOD * WORD_MOD := Nat.mul_le_mul_left _ (by omega)
    have hrecon : (xHi * WORD_MOD + xLo) * 2 ^ s3 / WORD_MOD * WORD_MOD +
        (xHi * WORD_MOD + xLo) * 2 ^ s3 % WORD_MOD =
        (xHi * WORD_MOD + xLo) * 2 ^ s3 % (WORD_MOD * WORD_MOD) := by
      rw [Nat.mul_comm ((xHi * WORD_MOD + xLo) * 2 ^ s3 / WORD_MOD) WORD_MOD,
        Nat.div_add_mod, Nat.mod_eq_of_lt hprodLt]
    have hge253 : 2 ^ 253 ≤ (xHi * WORD_MOD + xLo) * 2 ^ s3 / WORD_MOD := by
      rw [hhiVal]
      have hdivRw : xLo / 2 ^ (256 - s3) = xLo * 2 ^ s3 / WORD_MOD := by
        rw [show WORD_MOD = 2 ^ (256 - s3) * 2 ^ s3 from by
          unfold WORD_MOD
          rw [← Nat.pow_add]
          congr 1
          omega]
        exact (Nat.mul_div_mul_right _ _ (Nat.two_pow_pos s3)).symm
      rw [hdivRw]
      have h := cbrt512_normalized_hi_ge_253 xHi xLo hxHiPos hxHi hxLo
      simp only at h
      have hmodId :
          (xHi * 2 ^ s3 + xLo * 2 ^ s3 / WORD_MOD) % WORD_MOD =
            xHi * 2 ^ s3 + xLo * 2 ^ s3 / WORD_MOD := by
        rw [Nat.mod_eq_of_lt]
        rw [hhiVal] at hhiLt
        omega
      rw [hmodId] at h
      exact h
    refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
    · rw [hhiEq, hloEq]
      exact hrecon
    · rw [hhiEq]
      exact hge253
    · rw [hhiEq]
      exact hhiLt
    · rw [hloEq]
      exact hloLt

private theorem chain_6steps_upper (w m lo : Nat) (s d1 : Nat)
    (hm2 : 2 ≤ m) (hloPos : 0 < lo) (hlo : lo ≤ m) (hsPos : 0 < s)
    (hmlo : m * m * m ≤ w) (hmhi : w < (m + 1) * (m + 1) * (m + 1))
    (hd1 : cbrtStep w s - m ≤ d1) (h2d1 : 2 * d1 ≤ m)
    (h2d2 : 2 * nextD lo d1 ≤ lo)
    (h2d3 : 2 * nextD lo (nextD lo d1) ≤ lo)
    (h2d4 : 2 * nextD lo (nextD lo (nextD lo d1)) ≤ lo)
    (h2d5 : 2 * nextD lo (nextD lo (nextD lo (nextD lo d1))) ≤ lo)
    (hd6_le_1 : nextD lo
      (nextD lo (nextD lo (nextD lo (nextD lo d1)))) ≤ 1) :
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
    step_from_bound w m lo z2 (nextD lo d1) hm2 hloPos hlo hmhi hmz2 hd2
      (by omega)
  have hd4 : z4 - m ≤ nextD lo (nextD lo (nextD lo d1)) :=
    step_from_bound w m lo z3 _ hm2 hloPos hlo hmhi hmz3 hd3 (by omega)
  have hd5 : z5 - m ≤ nextD lo (nextD lo (nextD lo (nextD lo d1))) :=
    step_from_bound w m lo z4 _ hm2 hloPos hlo hmhi hmz4 hd4 (by omega)
  have hd6 :
      cbrtStep w z5 - m ≤
        nextD lo (nextD lo (nextD lo (nextD lo (nextD lo d1)))) :=
    step_from_bound w m lo z5 _ hm2 hloPos hlo hmhi hmz5 hd5 (by omega)
  have hd6_1 : cbrtStep w z5 - m ≤ 1 := Nat.le_trans hd6 hd6_le_1
  have : run6From w s = cbrtStep w z5 := rfl
  omega

private theorem octave_upper (w m s lo hi gap d1 : Nat)
    (hsPos : 0 < s)
    (hmlo : m * m * m ≤ w) (hmhi : w < (m + 1) * (m + 1) * (m + 1))
    (hlo : lo ≤ m) (hhi : m ≤ hi) (hm2 : 2 ≤ m) (hloPos : 0 < lo)
    (hgap_eq : max (s - lo) (hi - s) = gap)
    (hd1_formula :
      (gap * gap * (hi + 2 * s) + 3 * hi * (hi + 1)) / (3 * (s * s)) = d1)
    (h2d1_lo : 2 * d1 ≤ lo)
    (h2d2 : 2 * nextD lo d1 ≤ lo)
    (h2d3 : 2 * nextD lo (nextD lo d1) ≤ lo)
    (h2d4 : 2 * nextD lo (nextD lo (nextD lo d1)) ≤ lo)
    (h2d5 : 2 * nextD lo (nextD lo (nextD lo (nextD lo d1))) ≤ lo)
    (hd6_le1 : nextD lo
      (nextD lo (nextD lo (nextD lo (nextD lo d1)))) ≤ 1) :
    run6From w s ≤ m + 1 := by
  have hd1 : cbrtStep w s - m ≤ d1 := by
    have h := cbrt_d1_bound w m s lo hi hsPos hmlo hmhi hlo hhi
    rw [hgap_eq] at h
    simpa [hd1_formula] using h
  exact chain_6steps_upper w m lo s d1 hm2 hloPos hlo hsPos hmlo hmhi hd1
    (Nat.le_trans h2d1_lo hlo) h2d2 h2d3 h2d4 h2d5 hd6_le1

private theorem lo_le_icbrt_of_cube_le_pow (w lo : Nat) (k : Nat)
    (hlo_cube : lo * lo * lo ≤ 2 ^ k) (hw_lo : 2 ^ k ≤ w) :
    lo ≤ icbrt w := by
  have hlo_w : lo * lo * lo ≤ w := Nat.le_trans hlo_cube hw_lo
  by_cases h : lo ≤ icbrt w
  · exact h
  · exfalso
    have : icbrt w + 1 ≤ lo := by omega
    exact Nat.lt_irrefl w (Nat.lt_of_lt_of_le (icbrt_lt_succ_cube w)
      (Nat.le_trans (cube_monotone this) hlo_w))

private theorem icbrt_le_hi_of_pow_lt_cube (w hi : Nat) (k : Nat)
    (hhi_cube : 2 ^ (k + 1) ≤ (hi + 1) * (hi + 1) * (hi + 1))
    (hw_hi : w < 2 ^ (k + 1)) :
    icbrt w ≤ hi := by
  by_cases h : icbrt w ≤ hi
  · exact h
  · exfalso
    have : hi + 1 ≤ icbrt w := by omega
    have hmono := cube_monotone this
    exact Nat.lt_irrefl w (Nat.lt_of_lt_of_le hw_hi
      (Nat.le_trans hhi_cube (Nat.le_trans hmono (icbrt_cube_le w))))

theorem baseCase_NR_within_1ulp (w : Nat)
    (hw_lo : 2 ^ 251 ≤ w) (hw_hi : w < 2 ^ 254) :
    let m := icbrt w
    let z := run6From w baseCaseSeed
    m ≤ z ∧ z ≤ m + 1 := by
  simp only
  let s : Nat := baseCaseSeed
  let m := icbrt w
  have hmlo : m * m * m ≤ w := icbrt_cube_le w
  have hmhi : w < (m + 1) * (m + 1) * (m + 1) := icbrt_lt_succ_cube w
  have hw_pos : 0 < w := by omega
  have hsPos : 0 < s := by
    have hs_lo : 2 ^ 83 ≤ s := by
      change 2 ^ 83 ≤ baseCaseSeed
      exact baseCaseSeed_bounds.1
    omega
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
    simpa [s] using hmz
  refine ⟨hmz', ?_⟩
  by_cases h252 : w < 2 ^ 252
  · have hlo := lo_le_icbrt_of_cube_le_pow w octave251Lo 251 octave251_bounds.1 hw_lo
    have hhi := icbrt_le_hi_of_pow_lt_cube w octave251Hi 251 octave251_bounds.2 h252
    obtain ⟨h2d1, h2d2, h2d3, h2d4, h2d5, hd6_le1⟩ := octave251_chain_bounds
    simpa [s] using octave_upper w m s octave251Lo octave251Hi octave251Gap
      octave251D1 hsPos hmlo hmhi hlo hhi (Nat.le_trans octave251_lo_two_le hlo)
      (Nat.lt_of_lt_of_le (by omega : 0 < 2) octave251_lo_two_le)
      (by simpa [s] using octave251_gap_eq)
      (by simpa [s] using octave251_d1_formula_eq)
      h2d1 h2d2 h2d3 h2d4 h2d5 hd6_le1
  · by_cases h253 : w < 2 ^ 253
    · have hlo := lo_le_icbrt_of_cube_le_pow w octave252Lo 252 octave252_bounds.1
        (by omega)
      have hhi := icbrt_le_hi_of_pow_lt_cube w octave252Hi 252 octave252_bounds.2
        h253
      obtain ⟨h2d1, h2d2, h2d3, h2d4, h2d5, hd6_le1⟩ := octave252_chain_bounds
      simpa [s] using octave_upper w m s octave252Lo octave252Hi octave252Gap
        octave252D1 hsPos hmlo hmhi hlo hhi (Nat.le_trans octave252_lo_two_le hlo)
        (Nat.lt_of_lt_of_le (by omega : 0 < 2) octave252_lo_two_le)
        (by simpa [s] using octave252_gap_eq)
        (by simpa [s] using octave252_d1_formula_eq)
        h2d1 h2d2 h2d3 h2d4 h2d5 hd6_le1
    · have hlo := lo_le_icbrt_of_cube_le_pow w octave253Lo 253
        octave253_lo_cube_le_pow253 (by omega)
      have hhi := icbrt_le_hi_of_pow_lt_cube w M_TOP 253 m_top_cube_bounds.2 hw_hi
      obtain ⟨h2d1, h2d2, h2d3, h2d4, h2d5, hd6_le1⟩ := octave253_chain_bounds
      simpa [s] using octave_upper w m s octave253Lo M_TOP octave253Gap octave253D1
        hsPos hmlo hmhi hlo hhi (Nat.le_trans octave253_lo_two_le hlo)
        (Nat.lt_of_lt_of_le (by omega : 0 < 2) octave253_lo_two_le)
        (by simpa [s] using octave253_gap_eq)
        (by simpa [s] using octave253_d1_formula_eq)
        h2d1 h2d2 h2d3 h2d4 h2d5 hd6_le1

theorem two_le_of_pow83_le (m : Nat) (h : 2 ^ 83 ≤ m) : 2 ≤ m :=
  Nat.le_trans (show 2 ≤ 2 ^ 83 from by
    rw [show (2 : Nat) ^ 83 = 2 * 2 ^ 82 from by
      rw [show (83 : Nat) = 1 + 82 from rfl, Nat.pow_add]]
    omega) h

theorem cbrt512_evm_nr_step_eq_cbrtStep (w z : Nat)
    (hw : w < 2 ^ 254) (hz_lo : 2 ^ 83 ≤ z) (hz_hi : z < 2 ^ 88) :
    evmDiv (evmAdd (evmAdd (evmDiv w (evmMul z z)) z) z) 3 =
      cbrtStep w z ∧
    cbrtStep w z < 2 ^ 88 := by
  have hw_wm : w < WORD_MOD := by
    unfold WORD_MOD
    omega
  have hz_wm : z < WORD_MOD := by
    unfold WORD_MOD
    omega
  have hzz_wm : z * z < WORD_MOD := by
    calc z * z
        < 2 ^ 88 * 2 ^ 88 := Nat.lt_of_lt_of_le
            (Nat.mul_lt_mul_of_pos_left hz_hi (by omega))
            (Nat.mul_le_mul_right _ (Nat.le_of_lt hz_hi))
      _ = 2 ^ 176 := by rw [← Nat.pow_add]
      _ < WORD_MOD := by
        unfold WORD_MOD
        exact Nat.pow_lt_pow_right (by omega) (by omega)
  have hzz_ge : 2 ^ 166 ≤ z * z :=
    calc 2 ^ 166 = 2 ^ 83 * 2 ^ 83 := by rw [← Nat.pow_add]
      _ ≤ z * z := Nat.mul_le_mul hz_lo hz_lo
  have hdiv_lt : w / (z * z) < 2 ^ 88 :=
    (Nat.div_lt_iff_lt_mul (by omega : 0 < z * z)).mpr
      (calc w < 2 ^ 254 := hw
        _ = 2 ^ 88 * 2 ^ 166 := by rw [← Nat.pow_add]
        _ ≤ 2 ^ 88 * (z * z) := Nat.mul_le_mul_left _ hzz_ge)
  have hdiv_wm : w / (z * z) < WORD_MOD := by
    unfold WORD_MOD
    omega
  have hadd1_lt : w / (z * z) + z < WORD_MOD := by
    unfold WORD_MOD
    omega
  have hsum : w / (z * z) + 2 * z < WORD_MOD := by
    unfold WORD_MOD
    omega
  have hsum' : w / (z * z) + z + z < WORD_MOD := by
    omega
  have hmul_rr : evmMul z z = z * z := by
    rw [FormalYul.Preservation.evmMul_eq_mod_of_lt z z hz_wm hz_wm,
      Nat.mod_eq_of_lt hzz_wm]
  have hdiv_xrr : evmDiv w (evmMul z z) = w / (z * z) := by
    rw [hmul_rr]
    exact FormalYul.Preservation.evmDiv_eq_of_lt w (z * z) hw_wm (by omega) hzz_wm
  have hadd1 : evmAdd (evmDiv w (evmMul z z)) z = w / (z * z) + z := by
    rw [hdiv_xrr]
    exact FormalYul.Preservation.evmAdd_eq_of_lt _ _ hdiv_wm hz_wm hadd1_lt
  have hadd2 :
      evmAdd (evmAdd (evmDiv w (evmMul z z)) z) z =
        w / (z * z) + 2 * z := by
    rw [hadd1]
    rw [FormalYul.Preservation.evmAdd_eq_of_lt _ _ hadd1_lt hz_wm hsum']
    omega
  constructor
  · rw [hadd2]
    unfold cbrtStep
    exact FormalYul.Preservation.evmDiv_eq_of_lt _ 3 hsum
      (by omega) FormalYul.Preservation.three_lt_word
  · unfold cbrtStep
    exact (Nat.div_lt_iff_lt_mul (by omega : (0 : Nat) < 3)).mpr (by omega)

theorem cbrt512_base_case_math_bounds (xHi : Nat)
    (hx_lo : 2 ^ 253 ≤ xHi) (hx_hi : xHi < WORD_MOD) :
    let w := xHi / 4
    let m := icbrt w
    2 ^ 251 ≤ w ∧ w < 2 ^ 254 ∧ w < WORD_MOD ∧
    2 ^ 83 ≤ m ∧ m < 2 ^ 85 ∧
    m * m * m ≤ w ∧
    w - m * m * m ≤ 3 * (m * m) + 3 * m ∧
    m < WORD_MOD ∧ m * m < WORD_MOD ∧ m * m * m < WORD_MOD ∧
    3 * (m * m) < WORD_MOD ∧ 0 < 3 * (m * m) := by
  simp only
  let w := xHi / 4
  let m := icbrt w
  have hw_lo : 2 ^ 251 ≤ w := by
    show 2 ^ 251 ≤ xHi / 4
    omega
  have hw_hi : w < 2 ^ 254 := by
    show xHi / 4 < 2 ^ 254
    unfold WORD_MOD at hx_hi
    omega
  have hw_wm : w < WORD_MOD := by
    unfold WORD_MOD
    omega
  have hm_lo : 2 ^ 83 ≤ m :=
    lo_le_icbrt_of_cube_le_pow w (2 ^ 83) 251 pow83_cube_le_pow251 hw_lo
  have hm_hi : m < 2 ^ 85 := by
    show icbrt w < 2 ^ 85
    have := icbrt_le_hi_of_pow_lt_cube w (2 ^ 85 - 1) 253
      pow254_le_succ_pow85_sub_one_cube hw_hi
    omega
  have hm_wm : m < WORD_MOD := by
    unfold WORD_MOD
    omega
  have hm2_le : m * m ≤ (2 ^ 85 - 1) * (2 ^ 85 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hm2_wm : m * m < WORD_MOD := by
    have : (2 ^ 85 - 1) * (2 ^ 85 - 1) < WORD_MOD := pow85_sub_one_sq_lt_word
    omega
  have hm3_le : m * m * m ≤ (2 ^ 85 - 1) * (2 ^ 85 - 1) * (2 ^ 85 - 1) :=
    Nat.mul_le_mul hm2_le (by omega)
  have hm3_wm : m * m * m < WORD_MOD := by
    have : (2 ^ 85 - 1) * (2 ^ 85 - 1) * (2 ^ 85 - 1) < WORD_MOD :=
      pow85_sub_one_cube_lt_word
    omega
  have h3m2_wm : 3 * (m * m) < WORD_MOD := by
    unfold WORD_MOD
    omega
  have h3m2_pos : 0 < 3 * (m * m) := by
    have : 0 < m * m := Nat.mul_pos (by omega) (by omega)
    omega
  have hmcube_le : m * m * m ≤ w := icbrt_cube_le w
  have hmsucc_gt : w < (m + 1) * (m + 1) * (m + 1) := icbrt_lt_succ_cube w
  have hres_bound : w - m * m * m ≤ 3 * (m * m) + 3 * m := by
    have hcube :
        (m + 1) * (m + 1) * (m + 1) =
          m * m * m + 3 * (m * m) + 3 * m + 1 := by
      ring_nf
    rw [hcube] at hmsucc_gt
    omega
  exact ⟨hw_lo, hw_hi, hw_wm, hm_lo, hm_hi, hmcube_le, hres_bound, hm_wm,
    hm2_wm, hm3_wm, h3m2_wm, h3m2_pos⟩

theorem cbrt512_limb_hi_correct (xHi xLo : Nat)
    (hxHi : xHi < WORD_MOD) (hxLo : xLo < WORD_MOD) :
    let limbHi := evmOr (evmShl 84 (evmAnd 3 xHi)) (evmShr 172 xLo)
    limbHi = (xHi % 4) * 2 ^ 84 + xLo / 2 ^ 172 ∧
    limbHi < 2 ^ 86 ∧
    limbHi < WORD_MOD := by
  simp only
  have h3W : (3 : Nat) < WORD_MOD := FormalYul.Preservation.three_lt_word
  have hand : evmAnd 3 xHi = xHi % 4 := by
    rw [FormalYul.Preservation.evmAnd_eq_of_lt 3 xHi h3W hxHi]
    rw [Nat.and_comm]
    exact Nat.and_two_pow_sub_one_eq_mod xHi 2
  have hmod4 : xHi % 4 < 4 := Nat.mod_lt _ (by omega)
  have hmod4W : xHi % 4 < WORD_MOD := by
    unfold WORD_MOD
    omega
  have hprodLt : (xHi % 4) * 2 ^ 84 < 2 ^ 86 :=
    calc (xHi % 4) * 2 ^ 84
        < 4 * 2 ^ 84 := Nat.mul_lt_mul_of_pos_right hmod4 (Nat.two_pow_pos 84)
      _ = 2 ^ 86 := by rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add]
  have hprodW : (xHi % 4) * 2 ^ 84 < WORD_MOD := by
    unfold WORD_MOD
    omega
  have hshl : evmShl 84 (evmAnd 3 xHi) = (xHi % 4) * 2 ^ 84 := by
    rw [hand, FormalYul.Preservation.evmShl_eq_of_lt 84 (xHi % 4) (by omega) hmod4W]
    exact Nat.mod_eq_of_lt hprodW
  have hshr : evmShr 172 xLo = xLo / 2 ^ 172 :=
    FormalYul.Preservation.evmShr_eq_of_lt 172 xLo (by omega) hxLo
  have hdivLt : xLo / 2 ^ 172 < 2 ^ 84 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 172)]
    calc xLo < WORD_MOD := hxLo
      _ = 2 ^ 84 * 2 ^ 172 := by
        unfold WORD_MOD
        rw [← Nat.pow_add]
  have hdivW : xLo / 2 ^ 172 < WORD_MOD :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hxLo
  have hor : evmOr (evmShl 84 (evmAnd 3 xHi)) (evmShr 172 xLo) =
      (xHi % 4) * 2 ^ 84 + xLo / 2 ^ 172 := by
    rw [hshl, hshr, FormalYul.Preservation.evmOr_eq_of_lt _ _ hprodW hdivW]
    rw [show (xHi % 4) * 2 ^ 84 = (xHi % 4) <<< 84 from
      (Nat.shiftLeft_eq _ _).symm]
    exact (Nat.shiftLeft_add_eq_or_of_lt hdivLt (xHi % 4)).symm
  have hsumLt : (xHi % 4) * 2 ^ 84 + xLo / 2 ^ 172 < 2 ^ 86 :=
    calc (xHi % 4) * 2 ^ 84 + xLo / 2 ^ 172
        < (xHi % 4) * 2 ^ 84 + 2 ^ 84 := Nat.add_lt_add_left hdivLt _
      _ = ((xHi % 4) + 1) * 2 ^ 84 := (Nat.succ_mul _ _).symm
      _ ≤ 4 * 2 ^ 84 := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ 86 := by rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add]
  have hsumW : (xHi % 4) * 2 ^ 84 + xLo / 2 ^ 172 < WORD_MOD := by
    unfold WORD_MOD
    omega
  rw [hor]
  exact ⟨rfl, hsumLt, hsumW⟩

private theorem cbrt512_div_of_mul_add (d q r : Nat) (hd : 0 < d) :
    (d * q + r) / d = q + r / d := by
  rw [show d * q + r = r + q * d from by rw [Nat.mul_comm, Nat.add_comm],
    Nat.add_mul_div_right r q hd, Nat.add_comm]

private theorem cbrt512_mod_of_mul_add (d q r : Nat) :
    (d * q + r) % d = r % d := by
  rw [show d * q + r = r + q * d from by rw [Nat.mul_comm, Nat.add_comm],
    Nat.add_mul_mod_self_right]

private theorem cbrt512_mul_mod_mul_right (a n k : Nat) (hk : 0 < k) (hn : 0 < n) :
    (a * k) % (n * k) = (a % n) * k := by
  have hrw : a * k = (a % n) * k + (a / n) * (n * k) := by
    have h := Nat.div_add_mod a n
    calc a * k
        = (n * (a / n) + a % n) * k := by rw [h]
      _ = n * (a / n) * k + a % n * k := Nat.add_mul _ _ _
      _ = (a / n) * (n * k) + a % n * k := by
        rw [Nat.mul_comm n (a / n), Nat.mul_assoc]
      _ = a % n * k + (a / n) * (n * k) := Nat.add_comm _ _
  rw [hrw, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt (Nat.mul_lt_mul_of_pos_right (Nat.mod_lt a hn) hk)]

private theorem cbrt512_mul_pow86_mod_word (a : Nat) :
    (a * 2 ^ 86) % WORD_MOD = (a % 2 ^ 170) * 2 ^ 86 := by
  have hW : WORD_MOD = 2 ^ 170 * 2 ^ 86 := by
    unfold WORD_MOD
    rw [← Nat.pow_add]
  rw [hW]
  exact cbrt512_mul_mod_mul_right a (2 ^ 170) (2 ^ 86)
    (Nat.two_pow_pos 86) (Nat.two_pow_pos 170)

theorem cbrt512_karatsuba_quotient_correct
    (res limbHi d : Nat)
    (hres : res < WORD_MOD) (hlimb : limbHi < WORD_MOD)
    (hdGe : 2 ^ 86 ≤ d) (hdBound : d < 2 ^ 172)
    (hresBound : res < 2 ^ 171)
    (hlimbBound : limbHi < 2 ^ 86) :
    let n := evmOr (evmShl 86 res) limbHi
    let q0 := evmDiv n d
    let rem0 := evmMod n d
    let c := evmShr 170 res
    let q1 := evmAdd q0 (evmDiv (evmNot 0) d)
    let rem1 := evmAdd rem0 (evmAdd 1 (evmMod (evmNot 0) d))
    let q2 := evmAdd q1 (evmDiv rem1 d)
    let rem2 := evmMod rem1 d
    let out : Nat × Nat := if c = 0 then (q0, rem0) else (q2, rem2)
    out.1 = (res * 2 ^ 86 + limbHi) / d ∧
    out.2 = (res * 2 ^ 86 + limbHi) % d := by
  simp only
  have hdPos : 0 < d := by omega
  have hdW : d < WORD_MOD := by
    unfold WORD_MOD
    omega
  have hWFact : WORD_MOD = 2 ^ 170 * 2 ^ 86 := by
    unfold WORD_MOD
    rw [← Nat.pow_add]
  have hresModLt : res % 2 ^ 170 < 2 ^ 170 := Nat.mod_lt _ (Nat.two_pow_pos 170)
  have hnHiLt : (res % 2 ^ 170) * 2 ^ 86 < WORD_MOD := by
    rw [hWFact]
    exact Nat.mul_lt_mul_of_pos_right hresModLt (Nat.two_pow_pos 86)
  have hnLt : (res % 2 ^ 170) * 2 ^ 86 + limbHi < WORD_MOD := by
    calc (res % 2 ^ 170) * 2 ^ 86 + limbHi
        < (res % 2 ^ 170) * 2 ^ 86 + 2 ^ 86 := by omega
      _ = ((res % 2 ^ 170) + 1) * 2 ^ 86 := (Nat.succ_mul _ _).symm
      _ ≤ 2 ^ 170 * 2 ^ 86 := Nat.mul_le_mul_right _ (by omega)
      _ = WORD_MOD := hWFact.symm
  have hshlRes : evmShl 86 res = (res % 2 ^ 170) * 2 ^ 86 := by
    rw [FormalYul.Preservation.evmShl_eq_of_lt 86 res (by omega) hres]
    exact cbrt512_mul_pow86_mod_word res
  have horEq : evmOr ((res % 2 ^ 170) * 2 ^ 86) limbHi =
      (res % 2 ^ 170) * 2 ^ 86 + limbHi := by
    rw [FormalYul.Preservation.evmOr_eq_of_lt _ _ hnHiLt hlimb]
    rw [show (res % 2 ^ 170) * 2 ^ 86 = (res % 2 ^ 170) <<< 86 from
      (Nat.shiftLeft_eq _ _).symm]
    exact (Nat.shiftLeft_add_eq_or_of_lt hlimbBound (res % 2 ^ 170)).symm
  have hcEq : evmShr 170 res = res / 2 ^ 170 :=
    FormalYul.Preservation.evmShr_eq_of_lt 170 res (by omega) hres
  rw [hshlRes, horEq, hcEq]
  by_cases hcZero : res / 2 ^ 170 = 0
  · have hresSmall : res < 2 ^ 170 := by
      by_contra h
      have hge : 2 ^ 170 ≤ res := Nat.le_of_not_gt h
      have hpos : 0 < res / 2 ^ 170 := Nat.div_pos hge (Nat.two_pow_pos 170)
      omega
    have hmodRes : res % 2 ^ 170 = res := Nat.mod_eq_of_lt hresSmall
    have hnEq : (res % 2 ^ 170) * 2 ^ 86 + limbHi = res * 2 ^ 86 + limbHi := by
      rw [hmodRes]
    have hnFullLt : res * 2 ^ 86 + limbHi < WORD_MOD := by
      rw [← hnEq]
      exact hnLt
    simp only [hcZero, ↓reduceIte]
    constructor
    · rw [hnEq]
      exact FormalYul.Preservation.evmDiv_eq_of_lt _ d hnFullLt hdPos hdW
    · rw [hnEq]
      exact FormalYul.Preservation.evmMod_eq_of_lt _ d hnFullLt hdPos hdW
  · have hresGe : 2 ^ 170 ≤ res := by
      have hpos : 0 < res / 2 ^ 170 := Nat.pos_of_ne_zero hcZero
      exact (Nat.le_div_iff_mul_le (Nat.two_pow_pos 170)).mp hpos
    have hcOne : res / 2 ^ 170 = 1 := by
      have hcLe : res / 2 ^ 170 ≤ 1 :=
        Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 170)).mpr
          (by omega))
      omega
    have hnFullEq : res * 2 ^ 86 + limbHi =
        (res % 2 ^ 170) * 2 ^ 86 + limbHi + WORD_MOD := by
      have hdm := Nat.div_add_mod res (2 ^ 170)
      rw [hcOne] at hdm
      rw [hWFact]
      omega
    have hnDiv : evmDiv ((res % 2 ^ 170) * 2 ^ 86 + limbHi) d =
        ((res % 2 ^ 170) * 2 ^ 86 + limbHi) / d :=
      FormalYul.Preservation.evmDiv_eq_of_lt _ d hnLt hdPos hdW
    have hnMod : evmMod ((res % 2 ^ 170) * 2 ^ 86 + limbHi) d =
        ((res % 2 ^ 170) * 2 ^ 86 + limbHi) % d :=
      FormalYul.Preservation.evmMod_eq_of_lt _ d hnLt hdPos hdW
    have hnot0 : evmNot 0 = WORD_MOD - 1 :=
      FormalYul.Preservation.evmNot_eq_of_lt 0 FormalYul.Preservation.zero_lt_word
    have hWm1Lt : WORD_MOD - 1 < WORD_MOD := by
      unfold WORD_MOD
      omega
    have hwmDiv : evmDiv (WORD_MOD - 1) d = (WORD_MOD - 1) / d :=
      FormalYul.Preservation.evmDiv_eq_of_lt _ d hWm1Lt hdPos hdW
    have hwmMod : evmMod (WORD_MOD - 1) d = (WORD_MOD - 1) % d :=
      FormalYul.Preservation.evmMod_eq_of_lt _ d hWm1Lt hdPos hdW
    rw [hnot0, hnDiv, hnMod, hwmDiv, hwmMod]
    have hrwLt : (WORD_MOD - 1) % d < d := Nat.mod_lt _ hdPos
    have hrwW : (WORD_MOD - 1) % d < WORD_MOD := Nat.lt_of_lt_of_le hrwLt (by omega)
    have h1W : (1 : Nat) < WORD_MOD := FormalYul.Preservation.one_lt_word
    have h1rwSum : 1 + (WORD_MOD - 1) % d < WORD_MOD :=
      Nat.lt_of_le_of_lt (by omega : 1 + (WORD_MOD - 1) % d ≤ d) hdW
    have hadd1 : evmAdd 1 ((WORD_MOD - 1) % d) =
        1 + (WORD_MOD - 1) % d :=
      FormalYul.Preservation.evmAdd_eq_of_lt _ _ h1W hrwW h1rwSum
    have hr0Lt : ((res % 2 ^ 170) * 2 ^ 86 + limbHi) % d < d :=
      Nat.mod_lt _ hdPos
    have hr0W : ((res % 2 ^ 170) * 2 ^ 86 + limbHi) % d < WORD_MOD :=
      Nat.lt_of_lt_of_le hr0Lt (by omega)
    have hremSumW :
        ((res % 2 ^ 170) * 2 ^ 86 + limbHi) % d +
          (1 + (WORD_MOD - 1) % d) < WORD_MOD :=
      Nat.lt_of_lt_of_le (by omega : _ < 2 * d) (by unfold WORD_MOD; omega)
    have haddRem : evmAdd (((res % 2 ^ 170) * 2 ^ 86 + limbHi) % d)
        (1 + (WORD_MOD - 1) % d) =
        ((res % 2 ^ 170) * 2 ^ 86 + limbHi) % d +
          (1 + (WORD_MOD - 1) % d) :=
      FormalYul.Preservation.evmAdd_eq_of_lt _ _ hr0W h1rwSum hremSumW
    have hremSumLt2d :
        ((res % 2 ^ 170) * 2 ^ 86 + limbHi) % d +
          (1 + (WORD_MOD - 1) % d) < 2 * d := by
      omega
    have hdivRem : evmDiv
        (((res % 2 ^ 170) * 2 ^ 86 + limbHi) % d + (1 + (WORD_MOD - 1) % d)) d =
        (((res % 2 ^ 170) * 2 ^ 86 + limbHi) % d +
          (1 + (WORD_MOD - 1) % d)) / d :=
      FormalYul.Preservation.evmDiv_eq_of_lt _ d hremSumW hdPos hdW
    have hmodRem : evmMod
        (((res % 2 ^ 170) * 2 ^ 86 + limbHi) % d + (1 + (WORD_MOD - 1) % d)) d =
        (((res % 2 ^ 170) * 2 ^ 86 + limbHi) % d +
          (1 + (WORD_MOD - 1) % d)) % d :=
      FormalYul.Preservation.evmMod_eq_of_lt _ d hremSumW hdPos hdW
    have hq0W : ((res % 2 ^ 170) * 2 ^ 86 + limbHi) / d < WORD_MOD :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hnLt
    have hqwW : (WORD_MOD - 1) / d < WORD_MOD :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hWm1Lt
    have hq0Lt170 : ((res % 2 ^ 170) * 2 ^ 86 + limbHi) / d < 2 ^ 170 :=
      (Nat.div_lt_iff_lt_mul hdPos).mpr (Nat.lt_of_lt_of_le hnLt
        (by rw [hWFact]; exact Nat.mul_le_mul_left _ hdGe))
    have hqwLt170 : (WORD_MOD - 1) / d < 2 ^ 170 :=
      (Nat.div_lt_iff_lt_mul hdPos).mpr (Nat.lt_of_lt_of_le hWm1Lt
        (by rw [hWFact]; exact Nat.mul_le_mul_left _ hdGe))
    have hqSumW :
        ((res % 2 ^ 170) * 2 ^ 86 + limbHi) / d + (WORD_MOD - 1) / d <
          WORD_MOD := by
      have hlt : ((res % 2 ^ 170) * 2 ^ 86 + limbHi) / d +
          (WORD_MOD - 1) / d < 2 ^ 171 := by
        omega
      exact Nat.lt_of_lt_of_le hlt (by
        unfold WORD_MOD
        exact Nat.pow_le_pow_right (by omega) (by omega : 171 ≤ 256))
    have haddQ : evmAdd (((res % 2 ^ 170) * 2 ^ 86 + limbHi) / d)
        ((WORD_MOD - 1) / d) =
        ((res % 2 ^ 170) * 2 ^ 86 + limbHi) / d + (WORD_MOD - 1) / d :=
      FormalYul.Preservation.evmAdd_eq_of_lt _ _ hq0W hqwW hqSumW
    have hremDivLe1 :
        (((res % 2 ^ 170) * 2 ^ 86 + limbHi) % d +
          (1 + (WORD_MOD - 1) % d)) / d ≤ 1 :=
      Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hdPos).mpr hremSumLt2d)
    have hremDivW :
        (((res % 2 ^ 170) * 2 ^ 86 + limbHi) % d +
          (1 + (WORD_MOD - 1) % d)) / d < WORD_MOD := by
      exact Nat.lt_of_le_of_lt hremDivLe1 (by
        unfold WORD_MOD
        omega)
    have hfinalSumW :
        ((res % 2 ^ 170) * 2 ^ 86 + limbHi) / d + (WORD_MOD - 1) / d +
          (((res % 2 ^ 170) * 2 ^ 86 + limbHi) % d +
            (1 + (WORD_MOD - 1) % d)) / d < WORD_MOD := by
      have hlt : ((res % 2 ^ 170) * 2 ^ 86 + limbHi) / d +
          (WORD_MOD - 1) / d +
          (((res % 2 ^ 170) * 2 ^ 86 + limbHi) % d +
            (1 + (WORD_MOD - 1) % d)) / d < 2 ^ 171 + 1 := by
        omega
      exact Nat.lt_of_lt_of_le hlt (by
        unfold WORD_MOD
        omega)
    have haddFinal : evmAdd
        (((res % 2 ^ 170) * 2 ^ 86 + limbHi) / d + (WORD_MOD - 1) / d)
        ((((res % 2 ^ 170) * 2 ^ 86 + limbHi) % d +
          (1 + (WORD_MOD - 1) % d)) / d) =
        ((res % 2 ^ 170) * 2 ^ 86 + limbHi) / d + (WORD_MOD - 1) / d +
          (((res % 2 ^ 170) * 2 ^ 86 + limbHi) % d +
            (1 + (WORD_MOD - 1) % d)) / d :=
      FormalYul.Preservation.evmAdd_eq_of_lt _ _ hqSumW hremDivW hfinalSumW
    have hnFullDecomp : res * 2 ^ 86 + limbHi =
        d * (((res % 2 ^ 170) * 2 ^ 86 + limbHi) / d + (WORD_MOD - 1) / d) +
        (((res % 2 ^ 170) * 2 ^ 86 + limbHi) % d +
          (1 + (WORD_MOD - 1) % d)) := by
      rw [hnFullEq]
      have h1 := (Nat.div_add_mod ((res % 2 ^ 170) * 2 ^ 86 + limbHi) d).symm
      have h2 := (Nat.div_add_mod (WORD_MOD - 1) d).symm
      rw [Nat.mul_add]
      omega
    simp only [hcZero, ↓reduceIte]
    constructor
    · rw [hadd1, haddRem, hdivRem, haddQ, haddFinal, hnFullDecomp]
      exact (cbrt512_div_of_mul_add d _ _ hdPos).symm
    · rw [hadd1, haddRem, hmodRem, hnFullDecomp]
      exact (cbrt512_mod_of_mul_add d _ _).symm

private theorem cbrt512_cube_sum_expand (a b : Nat) :
    (a + b) * (a + b) * (a + b) =
      a * a * a + 3 * (a * a) * b + 3 * a * (b * b) + b * b * b := by
  ring_nf

private theorem cbrt512_R_cube_factor (m : Nat) :
    m * 2 ^ 86 * (m * 2 ^ 86) * (m * 2 ^ 86) = m * m * m * 2 ^ 258 := by
  have h258 : (2 : Nat) ^ 258 = 2 ^ 86 * (2 ^ 86 * 2 ^ 86) := by
    rw [show (258 : Nat) = 86 + (86 + 86) from rfl, Nat.pow_add, Nat.pow_add]
  rw [h258]
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

private theorem cbrt512_d_pow172_eq_3R_sq (m : Nat) :
    3 * (m * m) * 2 ^ 172 = 3 * (m * 2 ^ 86 * (m * 2 ^ 86)) := by
  have h172 : (2 : Nat) ^ 172 = 2 ^ 86 * 2 ^ 86 := by
    rw [show (172 : Nat) = 86 + 86 from rfl, Nat.pow_add]
  rw [h172]
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

private theorem cbrt512_x_norm_decomp (xHi xLo m3 : Nat)
    (hm3_le : m3 ≤ xHi / 4) :
    xHi * 2 ^ 256 + xLo =
      m3 * 2 ^ 258 +
      ((xHi / 4 - m3) * 2 ^ 86 + (xHi % 4 * 2 ^ 84 + xLo / 2 ^ 172)) *
        2 ^ 172 +
      xLo % 2 ^ 172 := by
  have h_xhi := Nat.div_add_mod xHi 4
  have h_xlo := Nat.div_add_mod xLo (2 ^ 172)
  have h258 : (2 : Nat) ^ 258 = 2 ^ 86 * 2 ^ 172 := by
    rw [show (258 : Nat) = 86 + 172 from rfl, Nat.pow_add]
  have h256 : (2 : Nat) ^ 256 = 2 ^ 84 * 2 ^ 172 := by
    rw [show (256 : Nat) = 84 + 172 from rfl, Nat.pow_add]
  have hn_expand :
      ((xHi / 4 - m3) * 2 ^ 86 + (xHi % 4 * 2 ^ 84 + xLo / 2 ^ 172)) *
          2 ^ 172 =
        (xHi / 4 - m3) * (2 ^ 86 * 2 ^ 172) +
          (xHi % 4 * 2 ^ 84 * 2 ^ 172 + xLo / 2 ^ 172 * 2 ^ 172) := by
    rw [Nat.add_mul, Nat.mul_assoc, Nat.add_mul, Nat.mul_assoc]
  rw [hn_expand]
  simp only [Nat.mul_assoc]
  rw [← h258, ← h256]
  omega

private theorem cbrt512_sq_sum_expand (a b : Nat) :
    (a + b) * (a + b) = a * a + 2 * a * b + b * b := by
  ring_nf

private theorem cbrt512_mm_sub_B_ge_eight (m B : Nat)
    (hmm_lo : 2 ^ 166 ≤ m * m)
    (hB_lt : B < 2 ^ 93) :
    8 ≤ m * m - B := by
  omega

private theorem cbrt512_tail_dom_by_mm_gap (R mm B c_tail : Nat)
    (hR_ge : 2 ^ 169 ≤ R)
    (hgap : 8 ≤ mm - B)
    (hctail_lt : c_tail < 2 ^ 172) :
    3 * R * B + c_tail < 3 * R * mm := by
  have hB_le_mm : B ≤ mm := by omega
  have hctail_dom : c_tail < 3 * R * (mm - B) := by
    calc c_tail < 2 ^ 172 := hctail_lt
      _ = 8 * 2 ^ 169 := by
          rw [show (172 : Nat) = 3 + 169 from rfl, Nat.pow_add]
      _ ≤ 8 * R := Nat.mul_le_mul_left _ hR_ge
      _ ≤ (3 * (mm - B)) * R := by
          apply Nat.mul_le_mul_right
          omega
      _ = 3 * R * (mm - B) := by
          simp only [Nat.mul_comm, Nat.mul_left_comm]
  calc 3 * R * B + c_tail < 3 * R * B + 3 * R * (mm - B) :=
        Nat.add_lt_add_left hctail_dom _
    _ = 3 * R * (B + (mm - B)) := by
        calc 3 * R * B + 3 * R * (mm - B)
            = R * (B * 3 + (mm - B) * 3) := by
                simp [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm]
          _ = R * ((B + (mm - B)) * 3) := by rw [← Nat.add_mul]
          _ = 3 * R * (B + (mm - B)) := by
                simp [Nat.mul_comm, Nat.mul_left_comm]
    _ = 3 * R * mm := by
        rw [Nat.add_sub_of_le hB_le_mm]

private theorem cbrt512_correction_le_rlo (rLo R : Nat) (hR_pos : 0 < R)
    (hR_gt : rLo < R) :
    rLo * rLo / R ≤ rLo := by
  cases Nat.eq_or_lt_of_le (Nat.zero_le rLo) with
  | inl h => rw [← h]; simp
  | inr h =>
    exact Nat.le_of_lt ((Nat.div_lt_iff_lt_mul hR_pos).mpr
      (Nat.mul_lt_mul_of_pos_left hR_gt h))

private theorem cbrt512_base_case_composition_bounds (xHi xLo : Nat)
    (hxhi_lo : 2 ^ 253 ≤ xHi) (hxhi_hi : xHi < WORD_MOD)
    (hxlo : xLo < WORD_MOD) :
    let m := icbrt (xHi / 4)
    let R := m * 2 ^ 86
    let d := 3 * (m * m)
    let limbHi := (xHi % 4) * 2 ^ 84 + xLo / 2 ^ 172
    let rLo := ((xHi / 4 - m * m * m) * 2 ^ 86 + limbHi) / d
    2 ^ 83 ≤ m ∧ m < 2 ^ 85 ∧ 2 ≤ m ∧ m < WORD_MOD ∧
    m * m * m ≤ xHi / 4 ∧
    xHi / 4 - m * m * m ≤ 3 * (m * m) + 3 * m ∧
    0 < d ∧ d < WORD_MOD ∧
    2 ^ 169 ≤ R ∧ R < 2 ^ 171 ∧ 0 < R ∧
    limbHi < 2 ^ 86 ∧ rLo < 2 ^ 87 := by
  simp only
  have hbc := cbrt512_base_case_math_bounds xHi hxhi_lo hxhi_hi
  simp only at hbc
  obtain ⟨_, _, _, hm_lo, hm_hi, hcube_le, hres_bound, hm_wm,
          _, _, hd_wm, hd_pos⟩ := hbc
  let m := icbrt (xHi / 4)
  have hm_pos : 2 ≤ m := two_le_of_pow83_le m hm_lo
  have hR_lo : 2 ^ 169 ≤ m * 2 ^ 86 :=
    calc 2 ^ 169 = 2 ^ 83 * 2 ^ 86 := by rw [← Nat.pow_add]
      _ ≤ m * 2 ^ 86 := Nat.mul_le_mul_right _ hm_lo
  have hR_hi : m * 2 ^ 86 < 2 ^ 171 :=
    calc m * 2 ^ 86
        < 2 ^ 85 * 2 ^ 86 := Nat.mul_lt_mul_of_pos_right hm_hi (Nat.two_pow_pos 86)
      _ = 2 ^ 171 := by rw [← Nat.pow_add]
  have hR_pos : 0 < m * 2 ^ 86 :=
    Nat.lt_of_lt_of_le (by omega : 0 < 2 ^ 169) hR_lo
  have hlimb : (xHi % 4) * 2 ^ 84 + xLo / 2 ^ 172 < 2 ^ 86 := by
    have hmod4 : xHi % 4 < 4 := Nat.mod_lt _ (by omega)
    have hdiv : xLo / 2 ^ 172 < 2 ^ 84 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 172)]
      calc xLo < WORD_MOD := hxlo
        _ = 2 ^ 84 * 2 ^ 172 := by
          unfold WORD_MOD
          rw [← Nat.pow_add]
    have hprod : (xHi % 4) * 2 ^ 84 < 2 ^ 86 :=
      calc (xHi % 4) * 2 ^ 84 < 4 * 2 ^ 84 :=
              Nat.mul_lt_mul_of_pos_right hmod4 (Nat.two_pow_pos 84)
        _ = 2 ^ 86 := by rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add]
    omega
  have hrLo_bound :
      ((xHi / 4 - m * m * m) * 2 ^ 86 +
        ((xHi % 4) * 2 ^ 84 + xLo / 2 ^ 172)) / (3 * (m * m)) < 2 ^ 87 := by
    rw [Nat.div_lt_iff_lt_mul hd_pos]
    calc ((xHi / 4 - m * m * m) * 2 ^ 86 +
            ((xHi % 4) * 2 ^ 84 + xLo / 2 ^ 172))
        < ((xHi / 4 - m * m * m) + 1) * 2 ^ 86 := by omega
      _ ≤ (3 * (m * m) + 3 * m + 1) * 2 ^ 86 := by
          apply Nat.mul_le_mul_right
          exact Nat.succ_le_succ hres_bound
      _ ≤ (2 * (3 * (m * m))) * 2 ^ 86 := by
          apply Nat.mul_le_mul_right
          have h2m : 2 * m ≤ m * m := Nat.mul_le_mul_right m (by omega)
          omega
      _ = 2 ^ 87 * (3 * (m * m)) := by
          rw [show (2 : Nat) ^ 87 = 2 * 2 ^ 86 from by
            rw [show (87 : Nat) = 1 + 86 from rfl, Nat.pow_add]]
          omega
  exact ⟨hm_lo, hm_hi, hm_pos, hm_wm, hcube_le, hres_bound,
    hd_pos, hd_wm, hR_lo, hR_hi, hR_pos, hlimb, hrLo_bound⟩

set_option exponentiation.threshold 1024 in
private theorem cbrt512_r_qc_succ2_cube_gt (xHi xLo : Nat)
    (hxhi_lo : 2 ^ 253 ≤ xHi) (hxhi_hi : xHi < WORD_MOD)
    (hxlo : xLo < WORD_MOD) :
    let w := xHi / 4
    let m := icbrt w
    let res := w - m * m * m
    let d := 3 * (m * m)
    let limbHi := (xHi % 4) * 2 ^ 84 + xLo / 2 ^ 172
    let rLo := (res * 2 ^ 86 + limbHi) / d
    let R := m * 2 ^ 86
    let correction := rLo * rLo / R
    let rQc := R + rLo - correction
    let xNorm := xHi * 2 ^ 256 + xLo
    xNorm < (rQc + 2) * (rQc + 2) * (rQc + 2) := by
  simp only
  obtain ⟨hm_lo, _, _, _, hcube_le_w, hres_bound,
          hd_pos, _, hR_lo, _, hR_pos, _, hrLo_bound⟩ :=
    cbrt512_base_case_composition_bounds xHi xLo hxhi_lo hxhi_hi hxlo
  let m := icbrt (xHi / 4)
  let w := xHi / 4
  let res := w - m * m * m
  let d := 3 * (m * m)
  let limbHi := (xHi % 4) * 2 ^ 84 + xLo / 2 ^ 172
  let rLo := (res * 2 ^ 86 + limbHi) / d
  let R := m * 2 ^ 86
  let c := rLo * rLo / R
  let remKq := (res * 2 ^ 86 + limbHi) % d
  let cTail := xLo % 2 ^ 172
  have hR_gt_rLo : rLo < R :=
    Nat.lt_of_lt_of_le hrLo_bound
      (Nat.le_trans (Nat.pow_le_pow_right (by omega) (by omega : 87 ≤ 169)) hR_lo)
  have hc_le : c ≤ rLo := cbrt512_correction_le_rlo rLo R hR_pos hR_gt_rLo
  have hrem_lt : remKq < d := Nat.mod_lt _ hd_pos
  have hctail_lt : cTail < 2 ^ 172 := Nat.mod_lt _ (Nat.two_pow_pos 172)
  have hx_decomp := cbrt512_x_norm_decomp xHi xLo (m * m * m) hcube_le_w
  have hn_full := Nat.div_add_mod (res * 2 ^ 86 + limbHi) d
  have hrem_ub : remKq * 2 ^ 172 + cTail < d * 2 ^ 172 + 2 ^ 172 := by
    have := Nat.mul_lt_mul_of_pos_right hrem_lt (Nat.two_pow_pos 172)
    omega
  have hx_ub : xHi * 2 ^ 256 + xLo <
      m * m * m * 2 ^ 258 + d * (rLo + 1) * 2 ^ 172 + 2 ^ 172 := by
    rw [hx_decomp]
    have hnum : (res * 2 ^ 86 + limbHi) = d * rLo + remKq := hn_full.symm
    rw [show ((xHi / 4 - m * m * m) * 2 ^ 86 +
        (xHi % 4 * 2 ^ 84 + xLo / 2 ^ 172)) = d * rLo + remKq from hnum]
    have hmul : (d * rLo + remKq) * 2 ^ 172 =
        d * rLo * 2 ^ 172 + remKq * 2 ^ 172 := Nat.add_mul _ _ _
    have hnext : d * (rLo + 1) * 2 ^ 172 =
        d * rLo * 2 ^ 172 + d * 2 ^ 172 := by
      rw [show d * (rLo + 1) = d * rLo + d * 1 from Nat.mul_add d rLo 1,
        Nat.mul_one, Nat.add_mul]
    rw [hmul, hnext]
    omega
  have hd_eq_3R2 := cbrt512_d_pow172_eq_3R_sq m
  have hrqc2_eq : m * 2 ^ 86 + rLo - rLo * rLo / (m * 2 ^ 86) + 2 =
      R + (rLo - c + 2) := by
    show R + rLo - c + 2 = R + (rLo - c + 2)
    omega
  rw [hrqc2_eq]
  rw [cbrt512_cube_sum_expand R (rLo - c + 2)]
  have hR3 := cbrt512_R_cube_factor m
  suffices h_suff : m * m * m * 2 ^ 258 + d * (rLo + 1) * 2 ^ 172 +
      2 ^ 172 ≤
      R * R * R + 3 * (R * R) * (rLo - c + 2) +
      3 * R * ((rLo - c + 2) * (rLo - c + 2)) +
      (rLo - c + 2) * (rLo - c + 2) * (rLo - c + 2) from
    Nat.lt_of_lt_of_le hx_ub h_suff
  have hs_ge_2 : 2 ≤ rLo - c + 2 := by omega
  rw [← hR3]
  have hd_rlo1 : d * (rLo + 1) * 2 ^ 172 = 3 * (R * R) * (rLo + 1) := by
    show 3 * (m * m) * (rLo + 1) * 2 ^ 172 =
      3 * (R * R) * (rLo + 1)
    rw [← hd_eq_3R2]
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [hd_rlo1]
  by_cases hc_le1 : c ≤ 1
  · have hs_ge_rlo1 : rLo + 1 ≤ rLo - c + 2 := by omega
    have h1 : 3 * (R * R) * (rLo + 1) ≤ 3 * (R * R) * (rLo - c + 2) :=
      Nat.mul_le_mul_left _ hs_ge_rlo1
    have hs_sq : 4 ≤ (rLo - c + 2) * (rLo - c + 2) :=
      Nat.mul_le_mul hs_ge_2 hs_ge_2
    have h12R : 2 ^ 172 ≤ 12 * R := by
      calc 2 ^ 172 = 2 * 2 ^ 171 := by
            rw [show (172 : Nat) = 1 + 171 from rfl, Nat.pow_add]
        _ ≤ 2 * (6 * R) := Nat.mul_le_mul_left _ (by omega)
        _ = 12 * R := by omega
    have h3Rs2 : 2 ^ 172 ≤ 3 * R * ((rLo - c + 2) * (rLo - c + 2)) :=
      calc 2 ^ 172 ≤ 12 * R := h12R
        _ = 3 * R * 4 := by omega
        _ ≤ 3 * R * ((rLo - c + 2) * (rLo - c + 2)) :=
            Nat.mul_le_mul_left _ hs_sq
    have step1 : R * R * R + 3 * (R * R) * (rLo + 1) + 2 ^ 172 ≤
        R * R * R + 3 * (R * R) * (rLo - c + 2) +
          3 * R * ((rLo - c + 2) * (rLo - c + 2)) :=
      Nat.add_le_add (Nat.add_le_add (Nat.le_refl _) h1) h3Rs2
    exact Nat.le_trans step1 (Nat.le_add_right _ _)
  · have hc_ge2 : 2 ≤ c := by omega
    have hcR_le : c * R ≤ rLo * rLo := Nat.div_mul_le_self _ _
    have hc_lt_32 : c < 32 := by
      have hcR_lt : c * R < 2 ^ 174 := Nat.lt_of_le_of_lt hcR_le
        (calc rLo * rLo
            ≤ rLo * 2 ^ 87 := Nat.mul_le_mul_left _ (Nat.le_of_lt hrLo_bound)
          _ < 2 ^ 87 * 2 ^ 87 :=
              Nat.mul_lt_mul_of_pos_right hrLo_bound (Nat.two_pow_pos 87)
          _ = 2 ^ 174 := by rw [← Nat.pow_add])
      have h174 : (2 : Nat) ^ 174 = 32 * 2 ^ 169 := by
        rw [show (174 : Nat) = 5 + 169 from rfl, Nat.pow_add]
      by_cases hc0 : c = 0
      · omega
      · exact Nat.lt_of_mul_lt_mul_right
          (calc c * R < 2 ^ 174 := hcR_lt
            _ = 32 * 2 ^ 169 := h174
            _ ≤ 32 * R := Nat.mul_le_mul_left _ hR_lo)
    have hcr_lt : c * rLo < 2 ^ 92 :=
      calc c * rLo < 32 * rLo := Nat.mul_lt_mul_of_pos_right hc_lt_32 (by omega)
        _ ≤ 32 * 2 ^ 87 := Nat.mul_le_mul_left _ (Nat.le_of_lt hrLo_bound)
        _ = 2 ^ 92 := by rw [show (32 : Nat) = 2 ^ 5 from rfl, ← Nat.pow_add]
    have h2cr : 2 * c * rLo < R := by
      calc 2 * c * rLo = 2 * (c * rLo) := Nat.mul_assoc 2 c rLo
        _ < 2 * 2 ^ 92 := Nat.mul_lt_mul_of_pos_left hcr_lt (by omega)
        _ = 2 ^ 93 := by rw [show (93 : Nat) = 1 + 92 from rfl, Nat.pow_add]
        _ ≤ R := Nat.le_trans (Nat.pow_le_pow_right (by omega) (by omega : 93 ≤ 169)) hR_lo
    have hsq_id : (rLo - c) * (rLo - c) + 2 * c * rLo = rLo * rLo + c * c := by
      suffices h : (↑((rLo - c) * (rLo - c) + 2 * c * rLo) : Int) =
          ↑(rLo * rLo + c * c) by exact_mod_cast h
      push_cast
      have hsub : (↑(rLo - c) : Int) = ↑rLo - ↑c := by omega
      rw [hsub]
      simp only [show (2 : Int) = 1 + 1 from rfl,
        Int.add_mul, Int.one_mul, Int.sub_mul, Int.mul_sub]
      simp only [Int.mul_comm]
      omega
    have hRc1_R : R * (c - 1) + R ≤ rLo * rLo := by
      calc R * (c - 1) + R
          = R * (c - 1) + R * 1 := by rw [Nat.mul_one]
        _ = R * (c - 1 + 1) := (Nat.mul_add R (c - 1) 1).symm
        _ = R * c := by congr 1; omega
        _ = c * R := Nat.mul_comm R c
        _ ≤ rLo * rLo := hcR_le
    have hrlc_sq : R * (c - 1) + 1 ≤ (rLo - c) * (rLo - c) := by
      have : rLo * rLo ≤ (rLo - c) * (rLo - c) + 2 * c * rLo := by
        rw [hsq_id]
        omega
      omega
    have hs_sq_ge : (rLo - c) * (rLo - c) + 4 ≤ (rLo - c + 2) * (rLo - c + 2) := by
      have h : (rLo - c + 2) * (rLo - c + 2) =
          (rLo - c) * (rLo - c) + 4 * (rLo - c) + 4 := by
        ring_nf
      omega
    have hs_sq_bound : R * (c - 1) + 5 ≤ (rLo - c + 2) * (rLo - c + 2) := by
      omega
    have h_3R_mul : 3 * R * (R * (c - 1) + 5) ≤
        3 * R * ((rLo - c + 2) * (rLo - c + 2)) :=
      Nat.mul_le_mul_left _ hs_sq_bound
    have h15R : 2 ^ 172 ≤ 15 * R := by
      calc 2 ^ 172 = 8 * 2 ^ 169 := by
            rw [show (172 : Nat) = 3 + 169 from rfl, Nat.pow_add]
        _ ≤ 8 * R := Nat.mul_le_mul_left _ hR_lo
        _ ≤ 15 * R := Nat.mul_le_mul_right _ (by omega)
    have hrlo1_split : 3 * (R * R) * (rLo + 1) =
        3 * (R * R) * (rLo - c + 2) + 3 * (R * R) * (c - 1) := by
      rw [← Nat.mul_add]
      congr 1
      omega
    rw [hrlo1_split]
    have hRR_assoc : 3 * (R * R) * (c - 1) = 3 * R * (R * (c - 1)) := by
      simp only [Nat.mul_assoc, Nat.mul_left_comm]
    rw [hRR_assoc]
    have step1 : 3 * R * (R * (c - 1)) + 2 ^ 172 ≤
        3 * R * (R * (c - 1)) + 15 * R := by omega
    have step2 : 3 * R * (R * (c - 1)) + 15 * R ≤
        3 * R * ((rLo - c + 2) * (rLo - c + 2)) := by
      calc 3 * R * (R * (c - 1)) + 15 * R
          = 3 * R * (R * (c - 1)) + 3 * R * 5 := by omega
        _ = 3 * R * (R * (c - 1) + 5) := (Nat.mul_add (3 * R) _ 5).symm
        _ ≤ 3 * R * ((rLo - c + 2) * (rLo - c + 2)) := h_3R_mul
    calc R * R * R + (3 * (R * R) * (rLo - c + 2) + 3 * R * (R * (c - 1))) +
          2 ^ 172
        ≤ R * R * R + (3 * (R * R) * (rLo - c + 2) +
            3 * R * ((rLo - c + 2) * (rLo - c + 2))) := by
          have := Nat.le_trans step1 step2
          omega
      _ ≤ R * R * R + 3 * (R * R) * (rLo - c + 2) +
            3 * R * ((rLo - c + 2) * (rLo - c + 2)) +
            (rLo - c + 2) * (rLo - c + 2) * (rLo - c + 2) := by omega

private theorem cbrt512_r_qc_pred_cube_le (xHi xLo : Nat)
    (hxhi_lo : 2 ^ 253 ≤ xHi) (hxhi_hi : xHi < WORD_MOD)
    (hxlo : xLo < WORD_MOD) :
    let w := xHi / 4
    let m := icbrt w
    let res := w - m * m * m
    let d := 3 * (m * m)
    let limbHi := (xHi % 4) * 2 ^ 84 + xLo / 2 ^ 172
    let rLo := (res * 2 ^ 86 + limbHi) / d
    let R := m * 2 ^ 86
    let correction := rLo * rLo / R
    let rQc := R + rLo - correction
    let xNorm := xHi * 2 ^ 256 + xLo
    (rQc - 1) * (rQc - 1) * (rQc - 1) ≤ xNorm := by
  simp only
  obtain ⟨_, _, _, _, hcube_le_w, _,
          _, _, hR_lo, _, _, _, _⟩ :=
    cbrt512_base_case_composition_bounds xHi xLo hxhi_lo hxhi_hi hxlo
  let m := icbrt (xHi / 4)
  let w := xHi / 4
  let res := w - m * m * m
  let d := 3 * (m * m)
  let limbHi := (xHi % 4) * 2 ^ 84 + xLo / 2 ^ 172
  let rLo := (res * 2 ^ 86 + limbHi) / d
  let R := m * 2 ^ 86
  let c := rLo * rLo / R
  let remKq := (res * 2 ^ 86 + limbHi) % d
  have hR_pos : 0 < R := by omega
  have hcR_lt : rLo * rLo < (c + 1) * R := by
    show rLo * rLo < (rLo * rLo / R + 1) * R
    have hdm := Nat.div_add_mod (rLo * rLo) R
    have hmod_lt := Nat.mod_lt (rLo * rLo) hR_pos
    calc rLo * rLo
        = R * (rLo * rLo / R) + rLo * rLo % R := hdm.symm
      _ < R * (rLo * rLo / R) + R := by omega
      _ = R * (rLo * rLo / R + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = (rLo * rLo / R + 1) * R := Nat.mul_comm _ _
  have hx_decomp := cbrt512_x_norm_decomp xHi xLo (m * m * m) hcube_le_w
  have hn_full := Nat.div_add_mod (res * 2 ^ 86 + limbHi) d
  have hnum : (res * 2 ^ 86 + limbHi) = d * rLo + remKq := hn_full.symm
  have hnum_mul : (d * rLo + remKq) * 2 ^ 172 =
      d * rLo * 2 ^ 172 + remKq * 2 ^ 172 := Nat.add_mul _ _ _
  have hx_lb : m * m * m * 2 ^ 258 + d * rLo * 2 ^ 172 ≤
      xHi * 2 ^ 256 + xLo := by
    rw [hx_decomp]
    rw [show ((xHi / 4 - m * m * m) * 2 ^ 86 +
        (xHi % 4 * 2 ^ 84 + xLo / 2 ^ 172)) = d * rLo + remKq from hnum]
    rw [hnum_mul]
    omega
  have hR3 := cbrt512_R_cube_factor m
  have hd_eq_3R2 := cbrt512_d_pow172_eq_3R_sq m
  have hx_lb2 : R * R * R + 3 * (R * R) * rLo ≤ xHi * 2 ^ 256 + xLo := by
    calc R * R * R + 3 * (R * R) * rLo
        = m * m * m * 2 ^ 258 + 3 * (m * m) * rLo * 2 ^ 172 := by
          rw [← hR3]
          show R * R * R + 3 * (R * R) * rLo =
            R * R * R + 3 * (m * m) * rLo * 2 ^ 172
          rw [← hd_eq_3R2]
          simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ = m * m * m * 2 ^ 258 + d * rLo * 2 ^ 172 := by rfl
      _ ≤ xHi * 2 ^ 256 + xLo := hx_lb
  by_cases hrloc : rLo ≤ c
  · have hrqc1_le : R + rLo - c - 1 ≤ R - 1 := by omega
    have hR1_le : R - 1 ≤ R := Nat.sub_le _ _
    calc (R + rLo - c - 1) * (R + rLo - c - 1) * (R + rLo - c - 1)
        ≤ (R - 1) * (R - 1) * (R - 1) := cube_monotone hrqc1_le
      _ ≤ R * R * R :=
          Nat.mul_le_mul (Nat.mul_le_mul hR1_le hR1_le) hR1_le
      _ ≤ R * R * R + 3 * (R * R) * rLo := Nat.le_add_right _ _
      _ ≤ xHi * 2 ^ 256 + xLo := hx_lb2
  · have hrqc1_eq : R + rLo - c - 1 = R + (rLo - c - 1) := by omega
    rw [hrqc1_eq, cbrt512_cube_sum_expand R (rLo - c - 1)]
    suffices h_suff : 3 * (R * R) * (rLo - c - 1) +
        3 * R * ((rLo - c - 1) * (rLo - c - 1)) +
        (rLo - c - 1) * (rLo - c - 1) * (rLo - c - 1) ≤
        3 * (R * R) * rLo from
      calc R * R * R + 3 * (R * R) * (rLo - c - 1) +
            3 * R * ((rLo - c - 1) * (rLo - c - 1)) +
            (rLo - c - 1) * (rLo - c - 1) * (rLo - c - 1)
          ≤ R * R * R + 3 * (R * R) * rLo := by omega
        _ ≤ xHi * 2 ^ 256 + xLo := hx_lb2
    have hrlo_split : 3 * (R * R) * rLo =
        3 * (R * R) * (rLo - c - 1) + 3 * (R * R) * (c + 1) := by
      rw [← Nat.mul_add]
      congr 1
      omega
    rw [hrlo_split]
    suffices h_core : 3 * R * ((rLo - c - 1) * (rLo - c - 1)) +
        (rLo - c - 1) * (rLo - c - 1) * (rLo - c - 1) ≤
        3 * (R * R) * (c + 1) by omega
    have ht_le_rLo : rLo - c - 1 ≤ rLo :=
      Nat.le_trans (Nat.sub_le _ _) (Nat.sub_le _ _)
    have ht_sq_lt_cR : (rLo - c - 1) * (rLo - c - 1) < (c + 1) * R :=
      Nat.lt_of_le_of_lt (Nat.mul_le_mul ht_le_rLo ht_le_rLo) hcR_lt
    have hrlo_eq : rLo = (rLo - c - 1) + (c + 1) := by omega
    have hrlo_sq := cbrt512_sq_sum_expand (rLo - c - 1) (c + 1)
    have h_gap : (rLo - c - 1) * (rLo - c - 1) +
        2 * (rLo - c - 1) * (c + 1) < (c + 1) * R := by
      have : (rLo - c - 1 + (c + 1)) * (rLo - c - 1 + (c + 1)) =
          (rLo - c - 1) * (rLo - c - 1) + 2 * (rLo - c - 1) * (c + 1) +
          (c + 1) * (c + 1) := hrlo_sq
      rw [← hrlo_eq] at this
      omega
    cases Nat.eq_or_lt_of_le (Nat.zero_le (rLo - c - 1)) with
    | inl ht0 =>
      rw [← ht0]
      simp
    | inr ht_pos =>
      rw [show (rLo - c - 1) * (rLo - c - 1) * (rLo - c - 1) =
          (rLo - c - 1) * ((rLo - c - 1) * (rLo - c - 1)) from
            Nat.mul_assoc _ _ _]
      have ht_cube_bound : (rLo - c - 1) * ((rLo - c - 1) * (rLo - c - 1)) <
          (rLo - c - 1) * ((c + 1) * R) :=
        Nat.mul_lt_mul_of_pos_left ht_sq_lt_cR ht_pos
      have hassoc1 : (rLo - c - 1) * ((c + 1) * R) =
          (rLo - c - 1) * (c + 1) * R :=
        (Nat.mul_assoc _ _ _).symm
      have h_gap2 : 2 * (rLo - c - 1) * (c + 1) <
          (c + 1) * R - (rLo - c - 1) * (rLo - c - 1) := by omega
      have hstep2 : 2 * (rLo - c - 1) * (c + 1) * R <
          ((c + 1) * R - (rLo - c - 1) * (rLo - c - 1)) * R :=
        Nat.mul_lt_mul_of_pos_right h_gap2 (by omega)
      have hchain : (rLo - c - 1) * ((c + 1) * R) <
          3 * R * ((c + 1) * R - (rLo - c - 1) * (rLo - c - 1)) := by
        rw [hassoc1]
        calc (rLo - c - 1) * (c + 1) * R
            ≤ 2 * (rLo - c - 1) * (c + 1) * R :=
              Nat.mul_le_mul_right R
                (Nat.mul_le_mul_right (c + 1) (Nat.le_mul_of_pos_left _ (by omega)))
          _ < ((c + 1) * R - (rLo - c - 1) * (rLo - c - 1)) * R := hstep2
          _ = R * ((c + 1) * R - (rLo - c - 1) * (rLo - c - 1)) := Nat.mul_comm _ _
          _ ≤ 3 * R * ((c + 1) * R - (rLo - c - 1) * (rLo - c - 1)) :=
              Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left R (by omega))
      have h_sum : 3 * R * ((rLo - c - 1) * (rLo - c - 1)) +
          3 * R * ((c + 1) * R - (rLo - c - 1) * (rLo - c - 1)) =
          3 * R * ((c + 1) * R) := by
        rw [← Nat.mul_add]
        congr 1
        omega
      have h_assoc : 3 * R * ((c + 1) * R) = 3 * (R * R) * (c + 1) := by
        suffices h : (↑(3 * R * ((c + 1) * R)) : Int) =
            ↑(3 * (R * R) * (c + 1)) by exact_mod_cast h
        push_cast
        simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      exact Nat.le_of_lt (calc
        3 * R * ((rLo - c - 1) * (rLo - c - 1)) +
            (rLo - c - 1) * ((rLo - c - 1) * (rLo - c - 1))
          < 3 * R * ((rLo - c - 1) * (rLo - c - 1)) +
            3 * R * ((c + 1) * R - (rLo - c - 1) * (rLo - c - 1)) := by
              omega
        _ = 3 * R * ((c + 1) * R) := h_sum
        _ = 3 * (R * R) * (c + 1) := h_assoc)

set_option exponentiation.threshold 1024 in
private theorem cbrt512_tight_numerator_bound (m : Nat) (hm : 2 ^ 83 ≤ m) :
    (3 * m + 1) * 2 ^ 86 ≤ 27 * (m * m) := by
  have h9m : 2 ^ 86 + 2 ^ 83 ≤ 9 * m := by omega
  have h9m_sub : 2 ^ 83 ≤ 9 * m - 2 ^ 86 := by omega
  have h_prod : 3 * 2 ^ 166 ≤ 3 * m * (9 * m - 2 ^ 86) :=
    calc 3 * 2 ^ 166
        = 3 * (2 ^ 83 * 2 ^ 83) := by
            rw [show (166 : Nat) = 83 + 83 from rfl, Nat.pow_add]
      _ ≤ 3 * (m * (9 * m - 2 ^ 86)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hm h9m_sub)
      _ = 3 * m * (9 * m - 2 ^ 86) := (Nat.mul_assoc 3 m _).symm
  have h_big : (2 : Nat) ^ 86 ≤ 3 * 2 ^ 166 := by
    calc 2 ^ 86 ≤ 1 * 2 ^ 166 := by
          show 2 ^ 86 ≤ 2 ^ 166
          exact Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ 3 * 2 ^ 166 := Nat.mul_le_mul_right _ (by omega)
  have h_split : 27 * (m * m) =
      3 * m * 2 ^ 86 + 3 * m * (9 * m - 2 ^ 86) := by
    rw [← Nat.mul_add]
    have h9m_eq : 2 ^ 86 + (9 * m - 2 ^ 86) = 9 * m := by omega
    rw [h9m_eq]
    suffices h : (↑(27 * (m * m)) : Int) = ↑(3 * m * (9 * m)) by
      exact_mod_cast h
    push_cast
    simp only [show (27 : Int) = 3 * 9 from rfl,
      Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have h_lhs : (3 * m + 1) * 2 ^ 86 = 3 * m * 2 ^ 86 + 2 ^ 86 := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
  rw [h_split, h_lhs]
  exact Nat.add_le_add_left (Nat.le_trans h_big h_prod) _

set_option exponentiation.threshold 1024 in
private theorem cbrt512_r_qc_le_r_max (xHi xLo : Nat)
    (hxhi_lo : 2 ^ 253 ≤ xHi) (hxhi_hi : xHi < WORD_MOD)
    (hxlo : xLo < WORD_MOD) :
    let w := xHi / 4
    let m := icbrt w
    let res := w - m * m * m
    let d := 3 * (m * m)
    let limbHi := (xHi % 4) * 2 ^ 84 + xLo / 2 ^ 172
    let rLo := (res * 2 ^ 86 + limbHi) / d
    let R := m * 2 ^ 86
    let correction := rLo * rLo / R
    let rQc := R + rLo - correction
    rQc ≤ R_MAX := by
  simp only
  obtain ⟨hm_lo, _, _, _, hcube_le_w, hres_bound,
          hd_pos, _, _, _, _, hlimb_bound, _⟩ :=
    cbrt512_base_case_composition_bounds xHi xLo hxhi_lo hxhi_hi hxlo
  let m := icbrt (xHi / 4)
  let w := xHi / 4
  let res := w - m * m * m
  let d := 3 * (m * m)
  let limbHi := (xHi % 4) * 2 ^ 84 + xLo / 2 ^ 172
  let rLo := (res * 2 ^ 86 + limbHi) / d
  let R := m * 2 ^ 86
  let c := rLo * rLo / R
  have h_rqc_le : R + rLo - c ≤ R + rLo := Nat.sub_le _ _
  by_cases hm_lt_top : m < M_TOP
  · have hrLo_tight : rLo ≤ 2 ^ 86 + 8 := by
      show (res * 2 ^ 86 + limbHi) / d ≤ 2 ^ 86 + 8
      suffices h : res * 2 ^ 86 + limbHi < (2 ^ 86 + 9) * d by
        exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hd_pos).mpr h)
      have h_num : res * 2 ^ 86 + limbHi <
          (3 * (m * m) + 3 * m + 1) * 2 ^ 86 := by
        calc res * 2 ^ 86 + limbHi
            < res * 2 ^ 86 + 2 ^ 86 := by omega
          _ = (res + 1) * 2 ^ 86 := by rw [Nat.add_mul, Nat.one_mul]
          _ ≤ (3 * (m * m) + 3 * m + 1) * 2 ^ 86 :=
              Nat.mul_le_mul_right _ (Nat.succ_le_succ hres_bound)
      have h27 := cbrt512_tight_numerator_bound m hm_lo
      have h_rhs : 3 * (m * m) * 2 ^ 86 + 27 * (m * m) =
          (2 ^ 86 + 9) * d := by
        show 3 * (m * m) * 2 ^ 86 + 27 * (m * m) = (2 ^ 86 + 9) * (3 * (m * m))
        omega
      calc res * 2 ^ 86 + limbHi
          < (3 * (m * m) + 3 * m + 1) * 2 ^ 86 := h_num
        _ = 3 * (m * m) * 2 ^ 86 + (3 * m + 1) * 2 ^ 86 := by
            have : (3 * (m * m) + (3 * m + 1)) * 2 ^ 86 =
                3 * (m * m) * 2 ^ 86 + (3 * m + 1) * 2 ^ 86 :=
              Nat.add_mul _ _ _
            omega
        _ ≤ 3 * (m * m) * 2 ^ 86 + 27 * (m * m) :=
            Nat.add_le_add_left h27 _
        _ = (2 ^ 86 + 9) * d := h_rhs
    have hR_le : R ≤ (M_TOP - 1) * 2 ^ 86 :=
      Nat.mul_le_mul_right _ (by omega : m ≤ M_TOP - 1)
    have h_sum : R + rLo ≤ M_TOP * 2 ^ 86 + 8 :=
      calc R + rLo
          ≤ (M_TOP - 1) * 2 ^ 86 + (2 ^ 86 + 8) :=
              Nat.add_le_add hR_le hrLo_tight
        _ = M_TOP * 2 ^ 86 + 8 := by
            have hM : 1 ≤ M_TOP := by
              unfold M_TOP
              omega
            omega
    have h_delta : 9 ≤ R_MAX - M_TOP * 2 ^ 86 := (r_lo_max_at_m_top).2.2
    have h_top_le : M_TOP * 2 ^ 86 + 8 ≤ R_MAX := by omega
    calc R + rLo - c ≤ R + rLo := h_rqc_le
      _ ≤ M_TOP * 2 ^ 86 + 8 := h_sum
      _ ≤ R_MAX := h_top_le
  · have hm_ge : M_TOP ≤ m := by omega
    have hw_hi : w < 2 ^ 254 := by
      show xHi / 4 < 2 ^ 254
      unfold WORD_MOD at hxhi_hi
      omega
    have hm_le : m ≤ M_TOP := by
      by_cases hm_le_top : m ≤ M_TOP
      · exact hm_le_top
      · exfalso
        have hsucc_le : M_TOP + 1 ≤ m := by omega
        have hmono : (M_TOP + 1) * (M_TOP + 1) * (M_TOP + 1) ≤ m * m * m :=
          cube_monotone hsucc_le
        have hm_cube_le : m * m * m ≤ w := hcube_le_w
        have htop := m_top_cube_bounds.2
        omega
    have hm_eq : m = M_TOP := Nat.le_antisymm hm_le hm_ge
    have h_rtop := r_lo_max_at_m_top
    let delta := R_MAX - M_TOP * 2 ^ 86
    have hres_le : res ≤ 2 ^ 254 - 1 - M_TOP * M_TOP * M_TOP := by
      show w - m * m * m ≤ 2 ^ 254 - 1 - M_TOP * M_TOP * M_TOP
      rw [hm_eq]
      omega
    have hd_eq : d = 3 * (M_TOP * M_TOP) := by
      show 3 * (m * m) = 3 * (M_TOP * M_TOP)
      rw [hm_eq]
    have hrLo_le : rLo ≤ delta + 1 := by
      show (res * 2 ^ 86 + limbHi) / d ≤ delta + 1
      have h_num : res * 2 ^ 86 + limbHi ≤
          (2 ^ 254 - 1 - M_TOP * M_TOP * M_TOP) * 2 ^ 86 + 2 ^ 86 - 1 := by
        have hlimb_le : limbHi ≤ 2 ^ 86 - 1 := by omega
        calc res * 2 ^ 86 + limbHi
            ≤ (2 ^ 254 - 1 - M_TOP * M_TOP * M_TOP) * 2 ^ 86 + (2 ^ 86 - 1) :=
              Nat.add_le_add (Nat.mul_le_mul_right _ hres_le) hlimb_le
          _ = (2 ^ 254 - 1 - M_TOP * M_TOP * M_TOP) * 2 ^ 86 + 2 ^ 86 - 1 := by
              omega
      rw [hd_eq]
      exact Nat.le_trans (Nat.div_le_div_right h_num) h_rtop.1
    by_cases hrLo_delta : rLo ≤ delta
    · have hR_eq : R = M_TOP * 2 ^ 86 := by
        show m * 2 ^ 86 = M_TOP * 2 ^ 86
        rw [hm_eq]
      calc R + rLo - c
          ≤ R + rLo := h_rqc_le
        _ = M_TOP * 2 ^ 86 + rLo := by rw [hR_eq]
        _ ≤ M_TOP * 2 ^ 86 + delta := Nat.add_le_add_left hrLo_delta _
        _ = R_MAX := by unfold delta; omega
    · have hrLo_eq : rLo = delta + 1 := by omega
      have hR_eq : R = M_TOP * 2 ^ 86 := by
        show m * 2 ^ 86 = M_TOP * 2 ^ 86
        rw [hm_eq]
      have hc_ge1 : 1 ≤ c := by
        show 1 ≤ rLo * rLo / R
        rw [hrLo_eq, hR_eq]
        exact h_rtop.2.1
      calc R + rLo - c
          ≤ R + rLo - 1 := Nat.sub_le_sub_left hc_ge1 (R + rLo)
        _ = M_TOP * 2 ^ 86 + (delta + 1) - 1 := by rw [hR_eq, hrLo_eq]
        _ = M_TOP * 2 ^ 86 + delta := by omega
        _ = R_MAX := by unfold delta; omega

private theorem cbrt512_quad_correction_ge_delta (R t delta : Nat)
    (hR_lo : 2 ^ 169 ≤ R) (hdelta_pos : 0 < delta)
    (hcube_upper : 3 * (R * R) * delta ≤ 3 * R * (t * t) + t * t * t)
    (hcube_lower :
      3 * R * (t * t) + t * t * t <
        3 * (R * R) * delta + 3 * (R * R) + 2 ^ 172) :
    delta * R ≤ (t + delta) * (t + delta) := by
  have hR_pos : 0 < R := by omega
  by_cases ht_sq : t * t < 6 * R
  · by_cases ht0 : t = 0
    · exfalso
      have h1 : 0 < 3 * (R * R) * delta :=
        Nat.mul_pos (Nat.mul_pos (by omega) (Nat.mul_pos hR_pos hR_pos)) hdelta_pos
      rw [ht0, show (0 : Nat) * 0 = 0 from rfl, Nat.mul_zero, Nat.add_zero] at hcube_upper
      omega
    · have ht_pos : 0 < t := by omega
      have ht3_bound : t * t * t < 6 * R * t := by
        rw [show t * t * t = t * (t * t) from Nat.mul_assoc _ _ _,
          show 6 * R * t = t * (6 * R) from by
            simp only [Nat.mul_comm, Nat.mul_left_comm]]
        exact Nat.mul_lt_mul_of_pos_left ht_sq ht_pos
      have h_bound : 3 * (R * R) * delta < 3 * R * (t * t + 2 * t) := by
        have h6eq : 6 * R * t = 3 * R * (2 * t) := by
          simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        calc 3 * (R * R) * delta
            ≤ 3 * R * (t * t) + t * t * t := hcube_upper
          _ < 3 * R * (t * t) + 6 * R * t := by omega
          _ = 3 * R * (t * t) + 3 * R * (2 * t) := by rw [h6eq]
          _ = 3 * R * (t * t + 2 * t) := by rw [← Nat.mul_add]
      have h_cancel : R * delta < t * t + 2 * t := by
        have h_assoc : 3 * (R * R) * delta = 3 * R * (R * delta) := by
          simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        rw [h_assoc] at h_bound
        exact Nat.lt_of_mul_lt_mul_left h_bound
      have h_sq_lb : t * t + 2 * t ≤ (t + delta) * (t + delta) := by
        rw [cbrt512_sq_sum_expand t delta]
        have : 2 * t ≤ 2 * t * delta := Nat.le_mul_of_pos_right _ hdelta_pos
        omega
      calc delta * R = R * delta := Nat.mul_comm _ _
        _ ≤ t * t + 2 * t := by omega
        _ ≤ (t + delta) * (t + delta) := h_sq_lb
  · have ht_sq_ge : 6 * R ≤ t * t := Nat.le_of_not_lt ht_sq
    have ht_pos : 0 < t := by
      cases Nat.eq_or_lt_of_le (Nat.zero_le t) with
      | inl h =>
        rw [← h] at ht_sq_ge
        omega
      | inr h => exact h
    have h3R2_gt : 2 ^ 172 ≤ 3 * (R * R) :=
      Nat.le_trans
        (Nat.le_trans
          (show 2 ^ 172 ≤ 2 ^ 169 * R from
            calc 2 ^ 172 = 2 ^ 169 * 2 ^ 3 := by rw [← Nat.pow_add]
              _ ≤ 2 ^ 169 * R := Nat.mul_le_mul_left _ (by omega : 2 ^ 3 ≤ R))
          (Nat.mul_le_mul_right _ hR_lo))
        (Nat.le_mul_of_pos_left _ (by omega))
    have h_Rdelta2 : t * t < R * (delta + 2) := by
      have h_rhs : 3 * (R * R) * delta + 3 * (R * R) + 2 ^ 172 ≤
          3 * (R * R) * (delta + 2) := by
        rw [show 3 * (R * R) * (delta + 2) =
          3 * (R * R) * delta + 3 * (R * R) * 2 from Nat.mul_add _ _ _]
        omega
      have h_3Rt2 : 3 * R * (t * t) < 3 * (R * R) * (delta + 2) :=
        calc 3 * R * (t * t) ≤ 3 * R * (t * t) + t * t * t := Nat.le_add_right _ _
          _ < 3 * (R * R) * delta + 3 * (R * R) + 2 ^ 172 := hcube_lower
          _ ≤ 3 * (R * R) * (delta + 2) := h_rhs
      have h_assoc : 3 * (R * R) * (delta + 2) = 3 * R * (R * (delta + 2)) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [h_assoc] at h_3Rt2
      exact Nat.lt_of_mul_lt_mul_left h_3Rt2
    have h_Rdelta_lb : t * t - 2 * R ≤ R * delta := by
      rw [show R * (delta + 2) = R * delta + R * 2 from Nat.mul_add _ _ _] at h_Rdelta2
      omega
    have h_6Rd : t * t ≤ 6 * (R * delta) := by
      have h5t2 : 12 * R ≤ 5 * (t * t) :=
        calc 12 * R ≤ 2 * (6 * R) := by omega
          _ ≤ 2 * (t * t) := Nat.mul_le_mul_left _ ht_sq_ge
          _ ≤ 5 * (t * t) := Nat.mul_le_mul_right _ (by omega)
      calc t * t ≤ 6 * (t * t) - 12 * R := by omega
        _ ≤ 6 * (t * t - 2 * R) := by omega
        _ ≤ 6 * (R * delta) := Nat.mul_le_mul_left _ h_Rdelta_lb
    have h_t3_le : t * t * t ≤ 6 * R * delta * t := by
      rw [show t * t * t = t * (t * t) from Nat.mul_assoc _ _ _,
        show 6 * R * delta * t = t * (6 * (R * delta)) from by
          simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]]
      exact Nat.mul_le_mul_left _ h_6Rd
    suffices h_3R : 3 * (R * R) * delta ≤ 3 * R * ((t + delta) * (t + delta)) by
      have h_assoc2 : 3 * (R * R) * delta = 3 * R * (R * delta) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [h_assoc2] at h_3R
      rw [show delta * R = R * delta from Nat.mul_comm _ _]
      exact Nat.le_of_mul_le_mul_left h_3R (by omega : 0 < 3 * R)
    have h_factor : 3 * R * (t * t) + 6 * R * delta * t + 3 * R * (delta * delta) =
        3 * R * (t * t + 2 * t * delta + delta * delta) := by
      have h6 : 6 * R * delta * t = 3 * R * (2 * t * delta) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [h6, ← Nat.mul_add, ← Nat.mul_add]
    calc 3 * (R * R) * delta
        ≤ 3 * R * (t * t) + t * t * t := hcube_upper
      _ ≤ 3 * R * (t * t) + 6 * R * delta * t := by omega
      _ ≤ 3 * R * (t * t) + 6 * R * delta * t + 3 * R * (delta * delta) :=
          Nat.le_add_right _ _
      _ = 3 * R * (t * t + 2 * t * delta + delta * delta) := h_factor
      _ = 3 * R * ((t + delta) * (t + delta)) := by
          congr 1
          exact (cbrt512_sq_sum_expand t delta).symm

private theorem cbrt512_perfect_cube_no_overshoot (s R rLo c : Nat)
    (hR_lo : 2 ^ 169 ≤ R) (hR_pos : 0 < R)
    (hc_def : c = rLo * rLo / R)
    (hc_strict : c < rLo)
    (hrqc_eq : R + rLo - c = s + 1)
    (hs_ge_R : R ≤ s)
    (hx_lb2 : R * R * R + 3 * (R * R) * rLo ≤ s * s * s)
    (hx_ub : s * s * s < R * R * R + 3 * (R * R) * (rLo + 1) + 2 ^ 172) :
    False := by
  have h_cube_expand := cbrt512_cube_sum_expand R (s - R)
  rw [Nat.add_sub_cancel' hs_ge_R] at h_cube_expand
  have hsR_eq : s - R = rLo - c - 1 := by
    have : R + (rLo - c) = s + 1 := by omega
    omega
  have hdelta_eq : rLo - (s - R) = c + 1 := by
    rw [hsR_eq]
    omega
  have hdelta_pos : 0 < rLo - (s - R) := hdelta_eq ▸ Nat.succ_pos _
  have hcube_upper : 3 * (R * R) * (rLo - (s - R)) ≤
      3 * R * ((s - R) * (s - R)) + (s - R) * (s - R) * (s - R) := by
    have h_from_lb : R * R * R + 3 * (R * R) * rLo ≤
        R * R * R + 3 * (R * R) * (s - R) +
          3 * R * ((s - R) * (s - R)) +
          (s - R) * (s - R) * (s - R) := by
      calc R * R * R + 3 * (R * R) * rLo ≤ s * s * s := hx_lb2
        _ = _ := h_cube_expand
    have h_split : 3 * (R * R) * rLo =
        3 * (R * R) * (s - R) + 3 * (R * R) * (rLo - (s - R)) := by
      rw [← Nat.mul_add]
      congr 1
      omega
    omega
  have hcube_lower : 3 * R * ((s - R) * (s - R)) +
      (s - R) * (s - R) * (s - R) <
      3 * (R * R) * (rLo - (s - R)) + 3 * (R * R) + 2 ^ 172 := by
    have h_from_ub : R * R * R + 3 * (R * R) * (s - R) +
        3 * R * ((s - R) * (s - R)) + (s - R) * (s - R) * (s - R) <
        R * R * R + 3 * (R * R) * (rLo + 1) + 2 ^ 172 := by
      calc R * R * R + 3 * (R * R) * (s - R) +
            3 * R * ((s - R) * (s - R)) + (s - R) * (s - R) * (s - R)
          = s * s * s := h_cube_expand.symm
        _ < R * R * R + 3 * (R * R) * (rLo + 1) + 2 ^ 172 := hx_ub
    have h_rlo_split : 3 * (R * R) * (rLo + 1) =
        3 * (R * R) * (s - R) + 3 * (R * R) * (rLo - (s - R)) +
          3 * (R * R) := by
      have : rLo + 1 = (s - R) + (rLo - (s - R)) + 1 := by omega
      rw [this, show (s - R) + (rLo - (s - R)) + 1 =
        (s - R) + ((rLo - (s - R)) + 1) from by omega]
      simp only [Nat.mul_add, Nat.mul_one, Nat.add_assoc]
    rw [h_rlo_split] at h_from_ub
    omega
  have h_qc := cbrt512_quad_correction_ge_delta R (s - R) (rLo - (s - R))
    hR_lo hdelta_pos hcube_upper hcube_lower
  rw [show s - R + (rLo - (s - R)) = rLo from by omega] at h_qc
  have hc_ge_delta : rLo - (s - R) ≤ c :=
    hc_def ▸ (Nat.le_div_iff_mul_le hR_pos).mpr h_qc
  omega

set_option exponentiation.threshold 1024 in
private theorem cbrt512_r_qc_no_overshoot_on_cubes (xHi xLo : Nat)
    (hxhi_lo : 2 ^ 253 ≤ xHi) (hxhi_hi : xHi < WORD_MOD)
    (hxlo : xLo < WORD_MOD) :
    let w := xHi / 4
    let m := icbrt w
    let res := w - m * m * m
    let d := 3 * (m * m)
    let limbHi := (xHi % 4) * 2 ^ 84 + xLo / 2 ^ 172
    let rLo := (res * 2 ^ 86 + limbHi) / d
    let R := m * 2 ^ 86
    let correction := rLo * rLo / R
    let rQc := R + rLo - correction
    let xNorm := xHi * 2 ^ 256 + xLo
    rQc * rQc * rQc > xNorm →
      icbrt xNorm * icbrt xNorm * icbrt xNorm < xNorm := by
  simp only
  obtain ⟨_, _, _, _, hcube_le_w, _,
          hd_pos, _, hR_lo, _, hR_pos, _, hrLo_bound⟩ :=
    cbrt512_base_case_composition_bounds xHi xLo hxhi_lo hxhi_hi hxlo
  let m := icbrt (xHi / 4)
  let w := xHi / 4
  let res := w - m * m * m
  let d := 3 * (m * m)
  let limbHi := (xHi % 4) * 2 ^ 84 + xLo / 2 ^ 172
  let rLo := (res * 2 ^ 86 + limbHi) / d
  let R := m * 2 ^ 86
  let c := rLo * rLo / R
  let remKq := (res * 2 ^ 86 + limbHi) % d
  let cTail := xLo % 2 ^ 172
  have hrem_lt : remKq < d := Nat.mod_lt _ hd_pos
  have hctail_lt : cTail < 2 ^ 172 := Nat.mod_lt _ (Nat.two_pow_pos 172)
  have hx_decomp := cbrt512_x_norm_decomp xHi xLo (m * m * m) hcube_le_w
  have hn_full := Nat.div_add_mod (res * 2 ^ 86 + limbHi) d
  have h_num_eq : (res * 2 ^ 86 + limbHi) = d * rLo + remKq := hn_full.symm
  have h_num_mul : (d * rLo + remKq) * 2 ^ 172 =
      d * rLo * 2 ^ 172 + remKq * 2 ^ 172 := Nat.add_mul _ _ _
  have hR3 := cbrt512_R_cube_factor m
  have hd_eq_3R2 := cbrt512_d_pow172_eq_3R_sq m
  have hrem_ub : remKq * 2 ^ 172 + cTail < d * 2 ^ 172 + 2 ^ 172 := by
    have := Nat.mul_lt_mul_of_pos_right hrem_lt (Nat.two_pow_pos 172)
    omega
  have hx_lb : m * m * m * 2 ^ 258 + d * rLo * 2 ^ 172 ≤
      xHi * 2 ^ 256 + xLo := by
    rw [hx_decomp]
    rw [show ((xHi / 4 - m * m * m) * 2 ^ 86 +
        (xHi % 4 * 2 ^ 84 + xLo / 2 ^ 172)) = d * rLo + remKq from h_num_eq]
    rw [h_num_mul]
    omega
  have hx_lb2 : R * R * R + 3 * (R * R) * rLo ≤ xHi * 2 ^ 256 + xLo := by
    calc R * R * R + 3 * (R * R) * rLo
        = m * m * m * 2 ^ 258 + 3 * (m * m) * rLo * 2 ^ 172 := by
          rw [← hR3]
          show R * R * R + 3 * (R * R) * rLo =
            R * R * R + 3 * (m * m) * rLo * 2 ^ 172
          rw [← hd_eq_3R2]
          simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ = m * m * m * 2 ^ 258 + d * rLo * 2 ^ 172 := by rfl
      _ ≤ xHi * 2 ^ 256 + xLo := hx_lb
  have hx_ub : xHi * 2 ^ 256 + xLo <
      R * R * R + 3 * (R * R) * (rLo + 1) + 2 ^ 172 := by
    have hx_ub_raw : xHi * 2 ^ 256 + xLo <
        m * m * m * 2 ^ 258 + d * (rLo + 1) * 2 ^ 172 + 2 ^ 172 := by
      rw [hx_decomp]
      rw [show ((xHi / 4 - m * m * m) * 2 ^ 86 +
          (xHi % 4 * 2 ^ 84 + xLo / 2 ^ 172)) = d * rLo + remKq from h_num_eq]
      rw [h_num_mul]
      have : d * (rLo + 1) * 2 ^ 172 = d * rLo * 2 ^ 172 + d * 2 ^ 172 := by
        rw [show d * (rLo + 1) = d * rLo + d * 1 from Nat.mul_add _ _ _,
          Nat.mul_one, Nat.add_mul]
      omega
    calc xHi * 2 ^ 256 + xLo
        < m * m * m * 2 ^ 258 + d * (rLo + 1) * 2 ^ 172 + 2 ^ 172 := hx_ub_raw
      _ = R * R * R + 3 * (R * R) * (rLo + 1) + 2 ^ 172 := by
          have hdr1 : d * (rLo + 1) * 2 ^ 172 = 3 * (R * R) * (rLo + 1) := by
            show 3 * (m * m) * (rLo + 1) * 2 ^ 172 =
              3 * (R * R) * (rLo + 1)
            rw [← hd_eq_3R2]
            simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
          rw [← hR3, hdr1]
  intro h_over
  let s := icbrt (xHi * 2 ^ 256 + xLo)
  have hcube_le := icbrt_cube_le (xHi * 2 ^ 256 + xLo)
  have hsucc_gt := icbrt_lt_succ_cube (xHi * 2 ^ 256 + xLo)
  by_cases h_not_perf : s * s * s < xHi * 2 ^ 256 + xLo
  · exact h_not_perf
  · exfalso
    have h_perf : s * s * s = xHi * 2 ^ 256 + xLo :=
      Nat.le_antisymm hcube_le (Nat.not_lt.mp h_not_perf)
    have hB := cbrt512_r_qc_pred_cube_le xHi xLo hxhi_lo hxhi_hi hxlo
    simp only at hB
    have hrqc_gt_s : s < R + rLo - c := by
      by_cases h : s < R + rLo - c
      · exact h
      · exfalso
        have h1 := cube_monotone (Nat.not_lt.mp h)
        rw [h_perf] at h1
        exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h_over h1)
    have hrqc1_le_s : R + rLo - c - 1 ≤ s := by
      by_cases h_gt : s < R + rLo - c - 1
      · exfalso
        have h1 := cube_monotone (show s + 1 ≤ R + rLo - c - 1 from by omega)
        have h2 := Nat.le_trans h1 hB
        exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hsucc_gt h2)
      · exact Nat.not_lt.mp h_gt
    have hrqc_eq : R + rLo - c = s + 1 := Nat.le_antisymm (by omega) (by omega)
    have hrLo_pos : 0 < rLo := by
      cases Nat.eq_or_lt_of_le (Nat.zero_le rLo) with
      | inr h => exact h
      | inl h =>
        exfalso
        have hrLo0 : rLo = 0 := h.symm
        have hc0 : c = 0 := by
          rw [show c = rLo * rLo / R from rfl, hrLo0]
          simp
        rw [hrLo0, hc0] at hrqc_eq
        have hR_cube_le : R * R * R ≤ xHi * 2 ^ 256 + xLo := by
          calc R * R * R ≤ R * R * R + 3 * (R * R) * 0 := by omega
            _ = R * R * R + 3 * (R * R) * rLo := by rw [hrLo0]
            _ ≤ _ := hx_lb2
        rw [← h_perf] at hR_cube_le
        have hsucc_eq : s + 1 = R := by omega
        have hsucc_cube : xHi * 2 ^ 256 + xLo < (s + 1) * (s + 1) * (s + 1) := hsucc_gt
        rw [hsucc_eq] at hsucc_cube
        omega
    have hR_gt_rLo : rLo < R :=
      Nat.lt_of_lt_of_le hrLo_bound
        (Nat.le_trans (Nat.pow_le_pow_right (by omega) (by omega : 87 ≤ 169)) hR_lo)
    have hc_strict : c < rLo :=
      (Nat.div_lt_iff_lt_mul hR_pos).mpr
        (Nat.mul_lt_mul_of_pos_left hR_gt_rLo hrLo_pos)
    have hs_ge_R : R ≤ s := by omega
    exact cbrt512_perfect_cube_no_overshoot s R rLo c hR_lo hR_pos rfl hc_strict
      hrqc_eq hs_ge_R (h_perf ▸ hx_lb2) (h_perf ▸ hx_ub)

theorem cbrt512_r_qc_properties (xHi xLo : Nat)
    (hxhi_lo : 2 ^ 253 ≤ xHi) (hxhi_hi : xHi < WORD_MOD)
    (hxlo : xLo < WORD_MOD) :
    let m := icbrt (xHi / 4)
    let res := xHi / 4 - m * m * m
    let d := 3 * (m * m)
    let limbHi := (xHi % 4) * 2 ^ 84 + xLo / 2 ^ 172
    let rLo := (res * 2 ^ 86 + limbHi) / d
    let R := m * 2 ^ 86
    let c := rLo * rLo / R
    let rQc := R + rLo - c
    let xNorm := xHi * WORD_MOD + xLo
    icbrt xNorm ≤ rQc + 1 ∧ rQc ≤ icbrt xNorm + 1 ∧
    rQc * rQc * rQc < WORD_MOD * WORD_MOD ∧
    (rQc * rQc * rQc > xNorm →
      icbrt xNorm * icbrt xNorm * icbrt xNorm < xNorm) := by
  simp only
  have hA := cbrt512_r_qc_succ2_cube_gt xHi xLo hxhi_lo hxhi_hi hxlo
  have hB := cbrt512_r_qc_pred_cube_le xHi xLo hxhi_lo hxhi_hi hxlo
  have hE1 := cbrt512_r_qc_le_r_max xHi xLo hxhi_lo hxhi_hi hxlo
  have hE2 := cbrt512_r_qc_no_overshoot_on_cubes xHi xLo hxhi_lo hxhi_hi hxlo
  simp only at hA hB hE1 hE2
  unfold WORD_MOD
  have hcube_le := icbrt_cube_le (xHi * 2 ^ 256 + xLo)
  have hsucc_gt := icbrt_lt_succ_cube (xHi * 2 ^ 256 + xLo)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Nat.not_lt.mp fun h =>
      absurd hA (Nat.not_lt.mpr (Nat.le_trans (cube_monotone h) hcube_le))
  · exact Nat.not_lt.mp fun h =>
      absurd hsucc_gt
        (Nat.not_lt.mpr (Nat.le_trans (cube_monotone (Nat.le_sub_one_of_lt h)) hB))
  · exact Nat.lt_of_le_of_lt (cube_monotone hE1) (by
      simpa [WORD_MOD] using r_max_cube_lt_wm2)
  · exact hE2

private theorem cube_expand_aux (m : Nat) :
    (m + 1) * (m + 1) * (m + 1) = m * m * m + 3 * m * m + 3 * m + 1 := by
  ring_nf

/-- 512-bit ceiling cube root. -/
noncomputable def cbrtUp512 (x : Nat) : Nat :=
  let r := icbrt x
  if r * r * r < x then r + 1 else r

/-- cbrtUp512 is the ceiling cbrt: x ≤ r³ and r is minimal. -/
theorem cbrtUp512_correct (x : Nat) (_hx : x < 2 ^ 512) :
    let r := cbrtUp512 x
    x ≤ r * r * r ∧ ∀ y, x ≤ y * y * y → r ≤ y := by
  simp only
  have hs_lo : icbrt x * icbrt x * icbrt x ≤ x := icbrt_cube_le x
  have hs_hi : x < (icbrt x + 1) * (icbrt x + 1) * (icbrt x + 1) := icbrt_lt_succ_cube x
  unfold cbrtUp512
  simp only
  by_cases hlt : icbrt x * icbrt x * icbrt x < x
  · -- s³ < x: ceiling is s + 1
    simp [hlt]
    exact ⟨by omega, fun y hy => by
      suffices h : ¬(y < icbrt x + 1) by omega
      intro hc
      have hc' : y ≤ icbrt x := by omega
      have := cube_monotone hc'; omega⟩
  · -- s³ = x: ceiling is s
    simp [hlt]
    have hseq : icbrt x * icbrt x * icbrt x = x := by omega
    exact ⟨by omega, fun y hy => by
      suffices h : ¬(y < icbrt x) by omega
      intro hc
      have hc' : y ≤ icbrt x - 1 := by omega
      have h1 := cube_monotone hc'
      have h2 : 0 < icbrt x := by omega
      have h3 := cube_expand_aux (icbrt x - 1)
      have h4 : (icbrt x - 1) + 1 = icbrt x := by omega
      rw [h4] at h3
      omega⟩

theorem gt512_correct (xHi xLo sqHi sqLo : Nat)
    (hxHi : xHi < WORD_MOD) (hxLo : xLo < WORD_MOD)
    (hsqHi : sqHi < WORD_MOD) (hsqLo : sqLo < WORD_MOD) :
    let cmp := evmOr (evmGt sqHi xHi)
      (evmAnd (evmEq sqHi xHi) (evmGt sqLo xLo))
    (cmp ≠ 0) ↔ (sqHi * WORD_MOD + sqLo > xHi * WORD_MOD + xLo) := by
  simp only
  rw [FormalYul.Preservation.evmGt_eq_of_lt sqHi xHi hsqHi hxHi,
    FormalYul.Preservation.evmEq_eq_of_lt sqHi xHi hsqHi hxHi,
    FormalYul.Preservation.evmGt_eq_of_lt sqLo xLo hsqLo hxLo]
  by_cases hgt : xHi < sqHi
  · have hneq : ¬sqHi = xHi := by omega
    simp only [hgt, ite_true, hneq, ite_false]
    have hor_nz : ∀ v, evmOr 1 (evmAnd 0 v) ≠ 0 := by
      intro v
      unfold evmOr evmAnd u256 WORD_MOD
      simp (config := { decide := true })
    constructor
    · intro _
      have h1 : xHi * WORD_MOD + WORD_MOD ≤ sqHi * WORD_MOD := by
        have := Nat.mul_le_mul_right WORD_MOD hgt
        rwa [Nat.succ_mul] at this
      omega
    · intro _
      exact hor_nz _
  · by_cases heq : sqHi = xHi
    · subst heq
      simp only [Nat.lt_irrefl, ite_false, ite_true]
      by_cases hgtLo : xLo < sqLo
      · simp only [hgtLo, ite_true]
        constructor
        · intro _
          omega
        · intro _
          unfold evmOr evmAnd u256 WORD_MOD
          simp (config := { decide := true })
      · simp only [hgtLo, ite_false]
        have hor_z : evmOr 0 (evmAnd 1 0) = 0 := by
          unfold evmOr evmAnd u256 WORD_MOD
          simp (config := { decide := true })
        constructor
        · intro h
          exact absurd hor_z h
        · intro h
          omega
    · have hlt : sqHi < xHi := by omega
      have hng : ¬xHi < sqHi := by omega
      simp only [hng, ite_false, heq, ite_false]
      have hor_z : ∀ v, evmOr 0 (evmAnd 0 v) = 0 := by
        intro v
        unfold evmOr evmAnd u256 WORD_MOD
        simp (config := { decide := true })
      constructor
      · intro h
        exact absurd (hor_z _) h
      · intro h
        have h1 : sqHi * WORD_MOD + WORD_MOD ≤ xHi * WORD_MOD := by
          have := Nat.mul_le_mul_right WORD_MOD hlt
          rwa [Nat.succ_mul] at this
        omega

theorem gt512_01 (xHi xLo sqHi sqLo : Nat)
    (hxHi : xHi < WORD_MOD) (hxLo : xLo < WORD_MOD)
    (hsqHi : sqHi < WORD_MOD) (hsqLo : sqLo < WORD_MOD) :
    let cmp := evmOr (evmGt sqHi xHi)
      (evmAnd (evmEq sqHi xHi) (evmGt sqLo xLo))
    cmp = 0 ∨ cmp = 1 :=
  FormalYul.Preservation.evmOr_01 _ _
    (FormalYul.Preservation.evmGt_01 _ _ hsqHi hxHi)
    (FormalYul.Preservation.evmAnd_01 _ _
      (FormalYul.Preservation.evmEq_01 _ _ hsqHi hxHi)
      (FormalYul.Preservation.evmGt_01 _ _ hsqLo hxLo))

theorem lt512_correct (xHi xLo sqHi sqLo : Nat)
    (hxHi : xHi < WORD_MOD) (hxLo : xLo < WORD_MOD)
    (hsqHi : sqHi < WORD_MOD) (hsqLo : sqLo < WORD_MOD) :
    let cmp := evmOr (evmLt sqHi xHi)
      (evmAnd (evmEq sqHi xHi) (evmLt sqLo xLo))
    (cmp ≠ 0) ↔ (sqHi * WORD_MOD + sqLo < xHi * WORD_MOD + xLo) := by
  simp only
  have hltHi : evmLt sqHi xHi = evmGt xHi sqHi := by
    rw [FormalYul.Preservation.evmLt_eq_of_lt sqHi xHi hsqHi hxHi,
      FormalYul.Preservation.evmGt_eq_of_lt xHi sqHi hxHi hsqHi]
  have heqComm : evmEq sqHi xHi = evmEq xHi sqHi := by
    rw [FormalYul.Preservation.evmEq_eq_of_lt sqHi xHi hsqHi hxHi,
      FormalYul.Preservation.evmEq_eq_of_lt xHi sqHi hxHi hsqHi]
    by_cases h : sqHi = xHi
    · simp [h]
    · simp [h, Ne.symm h]
  have hltLo : evmLt sqLo xLo = evmGt xLo sqLo := by
    rw [FormalYul.Preservation.evmLt_eq_of_lt sqLo xLo hsqLo hxLo,
      FormalYul.Preservation.evmGt_eq_of_lt xLo sqLo hxLo hsqLo]
  rw [hltHi, heqComm, hltLo]
  have hgt := gt512_correct sqHi sqLo xHi xLo hsqHi hsqLo hxHi hxLo
  simp only at hgt
  exact hgt

theorem lt512_01 (xHi xLo sqHi sqLo : Nat)
    (hxHi : xHi < WORD_MOD) (hxLo : xLo < WORD_MOD)
    (hsqHi : sqHi < WORD_MOD) (hsqLo : sqLo < WORD_MOD) :
    let cmp := evmOr (evmLt sqHi xHi)
      (evmAnd (evmEq sqHi xHi) (evmLt sqLo xLo))
    cmp = 0 ∨ cmp = 1 :=
  FormalYul.Preservation.evmOr_01 _ _
    (FormalYul.Preservation.evmLt_01 _ _ hsqHi hxHi)
    (FormalYul.Preservation.evmAnd_01 _ _
      (FormalYul.Preservation.evmEq_01 _ _ hsqHi hxHi)
      (FormalYul.Preservation.evmLt_01 _ _ hsqLo hxLo))

theorem mul512_high_word_general (a b : Nat) (ha : a < WORD_MOD) (hb : b < WORD_MOD) :
    let mm := evmMulmod a b (evmNot 0)
    let m := evmMul a b
    evmSub (evmSub mm m) (evmLt mm m) = a * b / WORD_MOD := by
  simp only
  have hNot0 : evmNot 0 = WORD_MOD - 1 := by
    simpa using
      FormalYul.Preservation.evmNot_eq_of_lt 0 FormalYul.Preservation.zero_lt_word
  have hWM1Pos : (0 : Nat) < WORD_MOD - 1 := by
    unfold WORD_MOD
    omega
  have hWM1Lt : WORD_MOD - 1 < WORD_MOD := by
    unfold WORD_MOD
    omega
  have hmm : evmMulmod a b (evmNot 0) = (a * b) % (WORD_MOD - 1) := by
    rw [hNot0]
    exact FormalYul.Preservation.evmMulmod_eq_of_lt a b (WORD_MOD - 1)
      ha hb hWM1Lt hWM1Pos
  have hm : evmMul a b = (a * b) % WORD_MOD :=
    FormalYul.Preservation.evmMul_eq_mod_of_lt a b ha hb
  rw [hmm, hm]
  have hqBound : a * b / WORD_MOD < WORD_MOD := by
    have : a * b < WORD_MOD * WORD_MOD :=
      Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt ha) hb (by unfold WORD_MOD; omega)
    exact Nat.div_lt_of_lt_mul this
  have hloBound : a * b % WORD_MOD < WORD_MOD := Nat.mod_lt _ (by unfold WORD_MOD; omega)
  have hhiEq :
      (a * b) % (WORD_MOD - 1) =
        (a * b / WORD_MOD + a * b % WORD_MOD) % (WORD_MOD - 1) := by
    have hqW :
        a * b / WORD_MOD * WORD_MOD =
          (WORD_MOD - 1) * (a * b / WORD_MOD) + a * b / WORD_MOD := by
      have hsc := Nat.sub_add_cancel
        (Nat.one_le_of_lt (show 1 < WORD_MOD from by unfold WORD_MOD; omega))
      have h := Nat.mul_add (a * b / WORD_MOD) (WORD_MOD - 1) 1
      rw [hsc, Nat.mul_one] at h
      rw [h, Nat.mul_comm (a * b / WORD_MOD) (WORD_MOD - 1)]
    have habEq :
        a * b =
          (WORD_MOD - 1) * (a * b / WORD_MOD) +
            (a * b / WORD_MOD + a * b % WORD_MOD) := by
      have hdiv := Nat.div_add_mod (a * b) WORD_MOD
      rw [Nat.mul_comm] at hdiv
      omega
    have step := Nat.mul_add_mod (WORD_MOD - 1) (a * b / WORD_MOD)
      (a * b / WORD_MOD + a * b % WORD_MOD)
    rw [← habEq] at step
    exact step
  by_cases hcase : a * b / WORD_MOD + a * b % WORD_MOD < WORD_MOD - 1
  · have hhiVal :
        (a * b) % (WORD_MOD - 1) = a * b / WORD_MOD + a * b % WORD_MOD := by
      rw [hhiEq, Nat.mod_eq_of_lt hcase]
    have hhiWm : (a * b) % (WORD_MOD - 1) < WORD_MOD := by omega
    have hge : a * b % WORD_MOD ≤ (a * b) % (WORD_MOD - 1) := by
      rw [hhiVal]
      exact Nat.le_add_left _ _
    have hltEq : evmLt ((a * b) % (WORD_MOD - 1)) (a * b % WORD_MOD) = 0 := by
      rw [FormalYul.Preservation.evmLt_eq_of_lt _ _ hhiWm hloBound]
      exact if_neg (Nat.not_lt.mpr hge)
    rw [hltEq]
    have hsub1 :
        evmSub ((a * b) % (WORD_MOD - 1)) (a * b % WORD_MOD) =
          (a * b) % (WORD_MOD - 1) - a * b % WORD_MOD :=
      FormalYul.Preservation.evmSub_eq_of_le _ _ hhiWm hge
    rw [hsub1]
    have hqEq :
        (a * b) % (WORD_MOD - 1) - a * b % WORD_MOD = a * b / WORD_MOD := by
      omega
    rw [hqEq]
    exact FormalYul.Preservation.evmSub_eq_of_le _ 0 hqBound (Nat.zero_le _)
  · have hcase' : WORD_MOD - 1 ≤ a * b / WORD_MOD + a * b % WORD_MOD :=
      Nat.not_lt.mp hcase
    have hqLe : a * b / WORD_MOD ≤ WORD_MOD - 2 := by
      have ha' : a ≤ WORD_MOD - 1 := by omega
      have hb' : b ≤ WORD_MOD - 1 := by omega
      have hab : a * b ≤ (WORD_MOD - 1) * (WORD_MOD - 1) := Nat.mul_le_mul ha' hb'
      have h1 : a * b / WORD_MOD ≤ (WORD_MOD - 1) * (WORD_MOD - 1) / WORD_MOD :=
        @Nat.div_le_div_right _ _ WORD_MOD hab
      suffices h : (WORD_MOD - 1) * (WORD_MOD - 1) / WORD_MOD = WORD_MOD - 2 by omega
      unfold WORD_MOD
      omega
    have hhiVal :
        (a * b) % (WORD_MOD - 1) =
          a * b / WORD_MOD + a * b % WORD_MOD - (WORD_MOD - 1) := by
      rw [hhiEq, Nat.mod_eq_sub_mod hcase', Nat.mod_eq_of_lt (by omega)]
    have hltLo : (a * b) % (WORD_MOD - 1) < a * b % WORD_MOD := by
      rw [hhiVal]
      omega
    have hhiWm : (a * b) % (WORD_MOD - 1) < WORD_MOD := by omega
    have hltEq : evmLt ((a * b) % (WORD_MOD - 1)) (a * b % WORD_MOD) = 1 := by
      rw [FormalYul.Preservation.evmLt_eq_of_lt _ _ hhiWm hloBound]
      exact if_pos hltLo
    rw [hltEq]
    have hsub1 :
        evmSub ((a * b) % (WORD_MOD - 1)) (a * b % WORD_MOD) =
          (a * b) % (WORD_MOD - 1) + WORD_MOD - a * b % WORD_MOD := by
      unfold evmSub u256
      simp [Nat.mod_eq_of_lt hhiWm, Nat.mod_eq_of_lt hloBound]
      exact Nat.mod_eq_of_lt (show
        (a * b) % (WORD_MOD - 1) + WORD_MOD - a * b % WORD_MOD < WORD_MOD by
          rw [hhiVal]
          omega)
    rw [hsub1]
    have hval :
        (a * b) % (WORD_MOD - 1) + WORD_MOD - a * b % WORD_MOD < WORD_MOD := by
      rw [hhiVal]
      omega
    have hsub2 :
        evmSub ((a * b) % (WORD_MOD - 1) + WORD_MOD - a * b % WORD_MOD) 1 =
          (a * b) % (WORD_MOD - 1) + WORD_MOD - a * b % WORD_MOD - 1 :=
      FormalYul.Preservation.evmSub_eq_of_le _ 1 hval (by
        rw [hhiVal]
        omega)
    rw [hsub2]
    rw [hhiVal]
    omega

theorem mul512_high_word (r : Nat) (hr : r < WORD_MOD) :
    let mm := evmMulmod r r (evmNot 0)
    let m := evmMul r r
    evmSub (evmSub mm m) (evmLt mm m) = r * r / WORD_MOD := by
  simpa using mul512_high_word_general r r hr hr

theorem mul512_low_word_general (a b : Nat) (ha : a < WORD_MOD) (hb : b < WORD_MOD) :
    evmMul a b = (a * b) % WORD_MOD :=
  FormalYul.Preservation.evmMul_eq_mod_of_lt a b ha hb

theorem mul512_low_word (r : Nat) (hr : r < WORD_MOD) :
    evmMul r r = r * r % WORD_MOD :=
  mul512_low_word_general r r hr hr

private theorem div_mul_le_mul_div (a b k : Nat) (hk : 0 < k) :
    a / k * b ≤ a * b / k := by
  have h1 : a / k * b * k ≤ a * b := by
    calc a / k * b * k
        = a / k * k * b := by rw [Nat.mul_assoc, Nat.mul_comm b k, ← Nat.mul_assoc]
      _ ≤ a * b := Nat.mul_le_mul_right b (Nat.div_mul_le_self a k)
  have h2 : a / k * b * k / k = a / k * b :=
    Nat.mul_div_cancel (a / k * b) hk
  calc a / k * b
      = a / k * b * k / k := h2.symm
    _ ≤ a * b / k := Nat.div_le_div_right h1

theorem cube512_correct (r : Nat) (hr : r < WORD_MOD)
    (hcube : r * r * r < WORD_MOD * WORD_MOD) :
    let mm1 := evmMulmod r r (evmNot 0)
    let r2Lo := evmMul r r
    let r2Hi := evmSub (evmSub mm1 r2Lo) (evmLt mm1 r2Lo)
    let mm2 := evmMulmod r2Lo r (evmNot 0)
    let r3Lo := evmMul r2Lo r
    let r3Hi := evmAdd (evmSub (evmSub mm2 r3Lo) (evmLt mm2 r3Lo)) (evmMul r2Hi r)
    r3Hi * WORD_MOD + r3Lo = r * r * r := by
  simp only
  have hWPos : (0 : Nat) < WORD_MOD := by
    unfold WORD_MOD
    omega
  have hR2Hi :
      evmSub (evmSub (evmMulmod r r (evmNot 0)) (evmMul r r))
        (evmLt (evmMulmod r r (evmNot 0)) (evmMul r r)) =
        r * r / WORD_MOD :=
    mul512_high_word r hr
  have hR2Lo : evmMul r r = (r * r) % WORD_MOD :=
    mul512_low_word r hr
  rw [hR2Hi, hR2Lo]
  have hPLt : (r * r) % WORD_MOD < WORD_MOD := Nat.mod_lt _ hWPos
  have hCubeHi :
      evmSub
        (evmSub (evmMulmod ((r * r) % WORD_MOD) r (evmNot 0))
          (evmMul ((r * r) % WORD_MOD) r))
        (evmLt (evmMulmod ((r * r) % WORD_MOD) r (evmNot 0))
          (evmMul ((r * r) % WORD_MOD) r)) =
        (r * r) % WORD_MOD * r / WORD_MOD :=
    mul512_high_word_general ((r * r) % WORD_MOD) r hPLt hr
  have hR3Lo : evmMul ((r * r) % WORD_MOD) r =
      ((r * r) % WORD_MOD * r) % WORD_MOD :=
    mul512_low_word_general ((r * r) % WORD_MOD) r hPLt hr
  rw [hCubeHi, hR3Lo]
  have hQLt : r * r / WORD_MOD < WORD_MOD :=
    Nat.div_lt_of_lt_mul (Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt hr) hr
      (by unfold WORD_MOD; omega))
  have hQrLt : r * r / WORD_MOD * r < WORD_MOD := by
    calc r * r / WORD_MOD * r
        ≤ r * r * r / WORD_MOD := div_mul_le_mul_div (r * r) r WORD_MOD hWPos
      _ < WORD_MOD := Nat.div_lt_of_lt_mul hcube
  have hevmMulHi : evmMul (r * r / WORD_MOD) r = r * r / WORD_MOD * r := by
    unfold evmMul u256
    simp [Nat.mod_eq_of_lt hQLt, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hQrLt]
  rw [hevmMulHi]
  have hR3Decomp :
      r * r * r = r * r / WORD_MOD * r * WORD_MOD + (r * r) % WORD_MOD * r := by
    have hEucl := Nat.div_add_mod (r * r) WORD_MOD
    calc r * r * r
        = (WORD_MOD * (r * r / WORD_MOD) + (r * r) % WORD_MOD) * r :=
          congrArg (· * r) hEucl.symm
      _ = WORD_MOD * (r * r / WORD_MOD) * r + (r * r) % WORD_MOD * r := Nat.add_mul _ _ r
      _ = r * r / WORD_MOD * WORD_MOD * r + (r * r) % WORD_MOD * r := by
          rw [Nat.mul_comm WORD_MOD (r * r / WORD_MOD)]
      _ = r * r / WORD_MOD * r * WORD_MOD + (r * r) % WORD_MOD * r := by
          rw [Nat.mul_assoc, Nat.mul_comm WORD_MOD r, ← Nat.mul_assoc]
  have hSumEq :
      (r * r) % WORD_MOD * r / WORD_MOD + r * r / WORD_MOD * r =
        r * r * r / WORD_MOD := by
    rw [hR3Decomp]
    rw [show
      r * r / WORD_MOD * r * WORD_MOD + (r * r) % WORD_MOD * r =
        (r * r) % WORD_MOD * r + r * r / WORD_MOD * r * WORD_MOD by omega]
    exact (Nat.add_mul_div_right ((r * r) % WORD_MOD * r)
      (r * r / WORD_MOD * r) hWPos).symm
  have hSumLt :
      (r * r) % WORD_MOD * r / WORD_MOD + r * r / WORD_MOD * r < WORD_MOD := by
    rw [hSumEq]
    exact Nat.div_lt_of_lt_mul hcube
  have hevmAdd : evmAdd ((r * r) % WORD_MOD * r / WORD_MOD) (r * r / WORD_MOD * r) =
      (r * r) % WORD_MOD * r / WORD_MOD + r * r / WORD_MOD * r :=
    FormalYul.Preservation.evmAdd_eq_of_lt _ _ (by omega) hQrLt hSumLt
  rw [hevmAdd]
  have hPrEucl := Nat.div_add_mod ((r * r) % WORD_MOD * r) WORD_MOD
  symm
  calc r * r * r
      = r * r / WORD_MOD * r * WORD_MOD + (r * r) % WORD_MOD * r := hR3Decomp
    _ = r * r / WORD_MOD * r * WORD_MOD
        + (WORD_MOD * ((r * r) % WORD_MOD * r / WORD_MOD)
          + (r * r) % WORD_MOD * r % WORD_MOD) := by
        rw [hPrEucl]
    _ = (r * r) % WORD_MOD * r / WORD_MOD * WORD_MOD
        + r * r / WORD_MOD * r * WORD_MOD
        + (r * r) % WORD_MOD * r % WORD_MOD := by
        rw [Nat.mul_comm WORD_MOD ((r * r) % WORD_MOD * r / WORD_MOD)]
        omega
    _ = ((r * r) % WORD_MOD * r / WORD_MOD + r * r / WORD_MOD * r) * WORD_MOD
        + (r * r) % WORD_MOD * r % WORD_MOD := by
        rw [← Nat.add_mul]

theorem cbrt512_floorCorrection_correct (xHi xLo r : Nat)
    (hxHi : xHi < WORD_MOD) (hxLo : xLo < WORD_MOD)
    (hr : r < WORD_MOD) (hcube : r * r * r < WORD_MOD * WORD_MOD)
    (hwithin :
      icbrt (xHi * WORD_MOD + xLo) ≤ r ∧
        r ≤ icbrt (xHi * WORD_MOD + xLo) + 1) :
    let r2Lo := evmMul r r
    let mm1 := evmMulmod r r (evmNot 0)
    let r2Hi := evmSub (evmSub mm1 r2Lo) (evmLt mm1 r2Lo)
    let mm2 := evmMulmod r2Lo r (evmNot 0)
    let r3Lo := evmMul r2Lo r
    let r3Hi := evmAdd (evmSub (evmSub mm2 r3Lo) (evmLt mm2 r3Lo)) (evmMul r2Hi r)
    let cmp := evmOr (evmGt r3Hi xHi) (evmAnd (evmEq r3Hi xHi) (evmGt r3Lo xLo))
    evmSub r cmp = icbrt (xHi * WORD_MOD + xLo) := by
  simp only
  let r2Lo := evmMul r r
  let mm1 := evmMulmod r r (evmNot 0)
  let r2Hi := evmSub (evmSub mm1 r2Lo) (evmLt mm1 r2Lo)
  let mm2 := evmMulmod r2Lo r (evmNot 0)
  let r3Lo := evmMul r2Lo r
  let r3Hi := evmAdd (evmSub (evmSub mm2 r3Lo) (evmLt mm2 r3Lo)) (evmMul r2Hi r)
  let cmp := evmOr (evmGt r3Hi xHi) (evmAnd (evmEq r3Hi xHi) (evmGt r3Lo xLo))
  have hcubeEq : r3Hi * WORD_MOD + r3Lo = r * r * r := by
    simpa [r2Lo, mm1, r2Hi, mm2, r3Lo, r3Hi] using cube512_correct r hr hcube
  have hr3Lo : r3Lo < WORD_MOD := by
    exact FormalYul.Preservation.evmMul_lt_WORD_MOD _ _
  have hr3Hi : r3Hi < WORD_MOD := by
    exact FormalYul.Preservation.evmAdd_lt_WORD_MOD _ _
  have hcmp01 : cmp = 0 ∨ cmp = 1 := by
    simpa [cmp] using gt512_01 xHi xLo r3Hi r3Lo hxHi hxLo hr3Hi hr3Lo
  have hcmpIff : (cmp ≠ 0) ↔ (r * r * r > xHi * WORD_MOD + xLo) := by
    have hgt := gt512_correct xHi xLo r3Hi r3Lo hxHi hxLo hr3Hi hr3Lo
    simp only at hgt
    rw [hcubeEq] at hgt
    simpa [cmp] using hgt
  change evmSub r cmp = icbrt (xHi * WORD_MOD + xLo)
  have hrCases :
      r = icbrt (xHi * WORD_MOD + xLo) ∨
        r = icbrt (xHi * WORD_MOD + xLo) + 1 := by
    omega
  rcases hrCases with hrEq | hrEq
  · have hNotGt : ¬(r * r * r > xHi * WORD_MOD + xLo) := by
      rw [hrEq]
      exact Nat.not_lt.mpr (icbrt_cube_le (xHi * WORD_MOD + xLo))
    have hcmpZero : cmp = 0 := by
      rcases hcmp01 with h | h
      · exact h
      · exfalso
        exact hNotGt (hcmpIff.mp (by omega))
    rw [hcmpZero, FormalYul.Preservation.evmSub_eq_of_le _ 0 hr (Nat.zero_le _)]
    exact hrEq
  · have hGt : r * r * r > xHi * WORD_MOD + xLo := by
      rw [hrEq]
      exact icbrt_lt_succ_cube (xHi * WORD_MOD + xLo)
    have hcmpOne : cmp = 1 := by
      rcases hcmp01 with h | h
      · exfalso
        have := hcmpIff.mpr hGt
        omega
      · exact h
    rw [hcmpOne, FormalYul.Preservation.evmSub_eq_of_le _ 1 hr (by rw [hrEq]; omega)]
    rw [hrEq]
    omega

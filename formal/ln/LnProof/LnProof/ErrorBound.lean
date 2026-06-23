import LnProof.ErrorBoundCore

set_option maxRecDepth 100000

/-!
# Public cut statement for the `lnWadToRay` error bound

The positive-shift region is covered by a single uniform residue argument: with
`lnErrorCoarsePosResidue = lnErrorCoarseGePosResidue = 0`, the coarse residue
predicate holds for every mantissa directly from the floor bracket
`1 ≤ posResidueGap` (`posResidueGap_bounds`), so no phase cover, no per-mantissa
cells, and no large `decide` over the octave are needed.  This yields the
`1706800000 / 10^9 = 1.7068` ulp cut; a sharper error bound and the minimal
bias/margin are tightened separately on top of this scaffold.
-/

namespace LnFloorCert

open LnGeneratedModel LnFloor LnExp LnPoly

attribute [local irreducible] model_ln_wad_evm

/-- Uniform coarse residue (full positive-shift): holds for every mantissa from
the floor bracket because `lnErrorCoarsePosResidue = 0`. -/
theorem PosShiftResidueOk_uniform {m c : Nat} (hmlo : MLO ≤ m) (hmhi : m < MHI)
    (hc : c < 160) :
    PosShiftResidueOk m c (toInt (lnTail (evmSub 160 c) m)) := by
  refine PosShiftResidueOk_of_gap (by omega) ?_
  unfold PosShiftResidueGapOk
  have hcoarse : (lnErrorCoarsePosResidue : Int) = 0 := by
    unfold lnErrorCoarsePosResidue; rfl
  rw [hcoarse]
  have hg := (posResidueGap_bounds hmlo hmhi hc).1
  refine Int.mul_nonneg (Int.mul_nonneg ?_ ?_) ?_
  · omega
  · unfold twoPow27I; decide
  · unfold lnErrorBoundDen; decide

/-- Uniform coarse residue (ge branch), `lnErrorCoarseGePosResidue = 0`. -/
theorem PosShiftGeResidueOk_uniform {m c : Nat} (hmlo : MLO ≤ m) (hmhi : m < MHI)
    (hc : c < 160) :
    PosShiftGeResidueOk m c (toInt (lnTail (evmSub 160 c) m)) := by
  refine PosShiftGeResidueOk_of_gap (by omega) ?_
  unfold PosShiftGeResidueGapOk
  have hcoarse : (lnErrorCoarseGePosResidue : Int) = 0 := by
    unfold lnErrorCoarseGePosResidue; rfl
  rw [hcoarse]
  have hg := (posResidueGap_bounds hmlo hmhi hc).1
  refine Int.mul_nonneg (Int.mul_nonneg ?_ ?_) ?_
  · omega
  · unfold twoPow27I; decide
  · unfold lnErrorBoundDen; decide

theorem model_ln_wad_positive_shift_ge_residue_or_direct_cert {x : Nat}
    (h1 : 1 ≤ x) (h2 : x < 2 ^ 255)
    (hclt : evmClz x < 160) (_hge : Sc ≤ mant x) :
    PosShiftGeResidueOk (mant x) (evmClz x) (toInt (model_ln_wad_evm x)) ∨
      PosShiftTopDirectOk 320 (mant x) (evmClz x) := by
  have hx256 : x < 2 ^ 256 := by omega
  have htail :
      model_ln_wad_evm x = lnTail (evmSub 160 (evmClz x)) (mant x) := by
    rw [model_eq_tail hx256]; rfl
  obtain ⟨me, hmlo, hmhi⟩ := mant_facts h1 h2
  have hmant_lo : MLO ≤ mant x := by unfold mant; rw [me]; exact hmlo
  have hmant_hi : mant x < MHI := by unfold mant; rw [me]; exact hmhi
  obtain ⟨hc1, _hc255⟩ := clz_bounds h1 h2
  rw [htail]
  exact Or.inl (PosShiftGeResidueOk_uniform hmant_lo hmant_hi hclt)

theorem model_ln_wad_positive_shift_lt_residue_or_direct_cert {x : Nat}
    (h1 : 1 ≤ x) (h2 : x < 2 ^ 255) (_hne : x ≠ 10 ^ 18)
    (hclt : evmClz x < 160) (_hlt : mant x < Sc) :
    PosShiftResidueOk (mant x) (evmClz x) (toInt (model_ln_wad_evm x)) ∨
      PosShiftTopDirectOk 320 (mant x) (evmClz x) := by
  have hx256 : x < 2 ^ 256 := by omega
  have htail :
      model_ln_wad_evm x = lnTail (evmSub 160 (evmClz x)) (mant x) := by
    rw [model_eq_tail hx256]; rfl
  obtain ⟨me, hmlo, hmhi⟩ := mant_facts h1 h2
  have hmant_lo : MLO ≤ mant x := by unfold mant; rw [me]; exact hmlo
  have hmant_hi : mant x < MHI := by unfold mant; rw [me]; exact hmhi
  obtain ⟨hc1, _hc255⟩ := clz_bounds h1 h2
  rw [htail]
  exact Or.inl (PosShiftResidueOk_uniform hmant_lo hmant_hi hclt)

theorem model_ln_wad_error_bound_upper_pos_shift {x : Nat}
    (h1 : 1 ≤ x) (h2 : x < 2 ^ 255) (hne : x ≠ 10 ^ 18)
    (hclt : evmClz x < 160) :
    CutLogWadRayLtRational x (toInt (model_ln_wad_evm x)) lnErrorBoundNum lnErrorBoundDen := by
  obtain ⟨me, hmlo, hmhi⟩ := mant_facts h1 h2
  have hmant_eq : mant x = x * 2 ^ (255 - Nat.log2 x) / 2 ^ 160 := me
  have hmant_lo : MLO ≤ mant x := by rw [hmant_eq]; exact hmlo
  have hmant_hi : mant x < MHI := by rw [hmant_eq]; exact hmhi
  obtain ⟨hc1, _hc255⟩ := clz_bounds h1 h2
  have hpos : 1 ≤ toInt (model_ln_wad_evm x) * (lnErrorBoundDen : Int) +
      (lnErrorBoundNum : Int) := by
    have hr0 := model_ln_wad_nonneg_of_clz_lt_160 h1 h2 hclt
    unfold lnErrorBoundDen lnErrorBoundNum
    omega
  unfold CutLogWadRayLtRational
  rw [if_pos hpos]
  change capLB (lnErrArg (toInt (model_ln_wad_evm x))) lnErrQ x (10 ^ 18)
  rcases Nat.lt_or_ge (mant x) Sc with hbranch | hbranch
  · exact model_ln_wad_positive_shift_lt_residue_or_direct h1 h2 hne hclt hbranch
      (model_ln_wad_positive_shift_lt_residue_or_direct_cert h1 h2 hne hclt hbranch)
  · exact model_ln_wad_positive_shift_ge_residue_or_direct h1 h2 hclt hbranch
      (model_ln_wad_positive_shift_ge_residue_or_direct_cert h1 h2 hclt hbranch)

/-- The model satisfies the `1.7068` ulp error-bound cut (uniform residue). -/
theorem model_ln_wad_error_bound_1_7068 {x : Nat} (h1 : 1 ≤ x) (h2 : x < 2 ^ 255) :
    let r := toInt (model_ln_wad_evm x)
    CutLeLogWadRay r x ∧
      CutLogWadRayLtRational x r lnErrorBoundNum lnErrorBoundDen := by
  by_cases hwad : x = 10 ^ 18
  · subst hwad
    rw [model_at_wad]
    constructor
    · unfold CutLeLogWadRay CutExpLe
      rw [if_pos (by decide)]
      exact capUB_diag QS_pos
    · exact cutLogWadRayLtRational_at_wad
  let r := toInt (model_ln_wad_evm x)
  change CutLeLogWadRay r x ∧
    CutLogWadRayLtRational x r lnErrorBoundNum lnErrorBoundDen
  constructor
  · exact (model_ln_wad_cut_spec h1 h2).1
  · by_cases hc160 : evmClz x = 160
    · exact model_ln_wad_error_bound_upper_c160 h1 h2 hwad hc160
    by_cases hrneg1 : r = -1
    · have hxlt : x < 10 ^ 18 := by
        exact (model_ln_wad_negative_iff h1 h2).mp (by omega)
      simpa [r, hrneg1] using cutLogWadRayLtRational_at_neg_one hxlt
    · by_cases hcgt : 160 < evmClz x
      · by_cases hr0 : 0 ≤ r
        · exact model_ln_wad_error_bound_upper_neg_shift_nonneg h1 h2 hwad hcgt hr0
        · have hrle : r ≤ -2 := by omega
          exact model_ln_wad_error_bound_upper_neg_shift_rec_ge h1 h2 hwad hcgt hrle
      · have hclt : evmClz x < 160 := by omega
        exact model_ln_wad_error_bound_upper_pos_shift h1 h2 hwad hclt

end LnFloorCert

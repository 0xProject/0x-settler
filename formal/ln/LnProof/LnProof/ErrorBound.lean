import LnProof.ErrorBoundCore
import LnProof.ErrCertLtBridge

set_option maxRecDepth 100000

/-!
# Public cut statement for the `lnWadToRay` error bound

The published cut is `1699000000 / 10^9 = 1.6990` ulp.  The positive lt octave
splits at the bracket-validity boundary: the mantissa window `[2^95, Sc-46]`
is covered by the degree-22 curved-cap Kronecker cell cover (`lt_pos_cut_reduced`
fed by `errLt_hred`), and the residue band `[Sc-45, Sc)` by the coarse residue
bound (`lo_lt_pos_exact`, whose octave budget binds at `Sc-45`).  The positive
ge octave and the negative shift keep their coarse residue bounds (which already
clear `1.6990`).  The coarse residue predicate holds for every mantissa directly
from the floor bracket `1 ≤ posResidueGap` (`posResidueGap_bounds`).
-/

namespace LnFloorCert

open LnYul LnFloor LnExp LnPoly

attribute [local irreducible] lnWadToRayBody

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

theorem lnWadToRayBody_positive_shift_ge_residue_or_direct_cert {x : Nat}
    (h1 : 1 ≤ x) (h2 : x < 2 ^ 255)
    (hclt : evmClz x < 160) (_hge : Sc ≤ mant x) :
    PosShiftGeResidueOk (mant x) (evmClz x) (toInt (lnWadToRayBody x)) ∨
      PosShiftTopDirectOk 320 (mant x) (evmClz x) := by
  have hx256 : x < 2 ^ 256 := by omega
  have htail :
      lnWadToRayBody x = lnTail (evmSub 160 (evmClz x)) (mant x) := by
    rw [lnWadToRayBody_eq_tail hx256]; rfl
  obtain ⟨me, hmlo, hmhi⟩ := mant_facts h1 h2
  have hmant_lo : MLO ≤ mant x := by unfold mant; rw [me]; exact hmlo
  have hmant_hi : mant x < MHI := by unfold mant; rw [me]; exact hmhi
  obtain ⟨hc1, _hc255⟩ := clz_bounds h1 h2
  rw [htail]
  exact Or.inl (PosShiftGeResidueOk_uniform hmant_lo hmant_hi hclt)

theorem lnWadToRayBody_positive_shift_lt_residue_or_direct_cert {x : Nat}
    (h1 : 1 ≤ x) (h2 : x < 2 ^ 255) (_hne : x ≠ 10 ^ 18)
    (hclt : evmClz x < 160) (_hlt : mant x < Sc) :
    PosShiftResidueOk (mant x) (evmClz x) (toInt (lnWadToRayBody x)) ∨
      PosShiftTopDirectOk 320 (mant x) (evmClz x) := by
  have hx256 : x < 2 ^ 256 := by omega
  have htail :
      lnWadToRayBody x = lnTail (evmSub 160 (evmClz x)) (mant x) := by
    rw [lnWadToRayBody_eq_tail hx256]; rfl
  obtain ⟨me, hmlo, hmhi⟩ := mant_facts h1 h2
  have hmant_lo : MLO ≤ mant x := by unfold mant; rw [me]; exact hmlo
  have hmant_hi : mant x < MHI := by unfold mant; rw [me]; exact hmhi
  obtain ⟨hc1, _hc255⟩ := clz_bounds h1 h2
  rw [htail]
  exact Or.inl (PosShiftResidueOk_uniform hmant_lo hmant_hi hclt)

theorem lnWadToRayBody_error_bound_upper_pos_shift {x : Nat}
    (h1 : 1 ≤ x) (h2 : x < 2 ^ 255) (hne : x ≠ 10 ^ 18)
    (hclt : evmClz x < 160) :
    CutLogWadRayLtRational x (toInt (lnWadToRayBody x)) lnErrorBoundNum lnErrorBoundDen := by
  obtain ⟨me, hmlo, hmhi⟩ := mant_facts h1 h2
  have hmant_eq : mant x = x * 2 ^ (255 - Nat.log2 x) / 2 ^ 160 := me
  have hmant_lo : MLO ≤ mant x := by rw [hmant_eq]; exact hmlo
  have hmant_hi : mant x < MHI := by rw [hmant_eq]; exact hmhi
  obtain ⟨hc1, _hc255⟩ := clz_bounds h1 h2
  have hpos : 1 ≤ toInt (lnWadToRayBody x) * (lnErrorBoundDen : Int) +
      (lnErrorBoundNum : Int) := by
    have hr0 := lnWadToRayBody_nonneg_of_clz_lt_160 h1 h2 hclt
    unfold lnErrorBoundDen lnErrorBoundNum
    omega
  unfold CutLogWadRayLtRational
  rw [if_pos hpos]
  change capLB (lnErrArg (toInt (lnWadToRayBody x))) lnErrQ x (10 ^ 18)
  rcases Nat.lt_or_ge (mant x) Sc with hbranch | hbranch
  · -- positive shift, lt octave: cell cut on `[2^95, Sc-46]`, residue band on `[Sc-45, Sc)`
    rcases Nat.lt_or_ge (mant x) (Sc - 45) with hcell | hband
    · -- cell domain: `mant x < Sc - 45` ⟹ `mant x + 46 ≤ Sc`
      have hx256 : x < 2 ^ 256 := by omega
      have htail : lnWadToRayBody x = lnTail (evmSub 160 (evmClz x)) (mant x) := by
        rw [lnWadToRayBody_eq_tail hx256]; rfl
      have hh2 : mant x + 46 ≤ Sc := by omega
      have hmin : posPhaseNatLt (mant x) (evmClz x) + minPosAvail ≤
          lnErrArg (toInt (lnWadToRayBody x)) := by
        have hp := posPhaseNatLt_minAvail_le_lnErrArg hmant_lo (by omega : mant x < Sc) hclt
        rw [← htail] at hp; exact hp
      have hxtop : x ≤ posTopX (evmClz x) (mant x) := by
        have hw := mant_window_le h1 h2 (by omega : evmClz x ≤ 160)
        have hwpos : 0 < (mant x + 1) * 2 ^ (160 - evmClz x) :=
          Nat.mul_pos (Nat.succ_pos _) (Nat.pow_pos (by decide))
        unfold posTopX; omega
      have hcut := lt_pos_cut_reduced (m := mant x) (c := evmClz x) (x := x)
        (r := toInt (lnWadToRayBody x)) hmant_lo hh2 hc1 hclt hmin hxtop
        (errLt_hred hmant_lo hh2)
      refine capLB_weaken (p := lnErrArg (toInt (lnWadToRayBody x))) (q := lnErrQ)
        (y := wadRayNum x) (w := wadRayStrictDen) (y' := x) (w' := 10 ^ 18)
        (by decide) hcut ?_
      unfold wadRayNum wadRayStrictDen
      have hsub : (10 ^ 31 - 10 : Nat) ≤ 10 ^ 31 := by omega
      calc x * (10 ^ 18 * (10 ^ 31 - 10))
          ≤ x * (10 ^ 18 * 10 ^ 31) :=
            Nat.mul_le_mul (Nat.le_refl _) (Nat.mul_le_mul (Nat.le_refl _) hsub)
        _ = x * 10 ^ 31 * 10 ^ 18 := by
            simp only [Nat.mul_comm, Nat.mul_left_comm]
    · -- residue band: `Sc - 45 ≤ mant x < Sc`
      exact lnWadToRayBody_positive_shift_lt_residue_or_direct h1 h2 hne hclt hbranch hband
        (lnWadToRayBody_positive_shift_lt_residue_or_direct_cert h1 h2 hne hclt hbranch)
  · exact lnWadToRayBody_positive_shift_ge_residue_or_direct h1 h2 hclt hbranch
      (lnWadToRayBody_positive_shift_ge_residue_or_direct_cert h1 h2 hclt hbranch)

/-- The body decomposition satisfies the `1.6990` ulp error-bound cut: the lt octave is
covered by the degree-22 curved-cap cell cover on `[2^95, Sc-46]` and a residue
band on `[Sc-45, Sc)`, the ge octave by the coarse residue bound, and the
negative shift by its coarse residue bound. -/
theorem lnWadToRayBody_error_bound_1_6986 {x : Nat} (h1 : 1 ≤ x) (h2 : x < 2 ^ 255) :
    let r := toInt (lnWadToRayBody x)
    CutLeLogWadRay r x ∧
      CutLogWadRayLtRational x r lnErrorBoundNum lnErrorBoundDen := by
  by_cases hwad : x = 10 ^ 18
  · subst hwad
    rw [lnWadToRayBody_one_wad]
    constructor
    · unfold CutLeLogWadRay CutExpLe
      rw [if_pos (by decide)]
      exact capUB_diag QS_pos
    · exact cutLogWadRayLtRational_at_wad
  let r := toInt (lnWadToRayBody x)
  change CutLeLogWadRay r x ∧
    CutLogWadRayLtRational x r lnErrorBoundNum lnErrorBoundDen
  constructor
  · exact (lnWadToRayBody_cut_spec h1 h2).1
  · by_cases hc160 : evmClz x = 160
    · exact lnWadToRayBody_error_bound_upper_c160 h1 h2 hwad hc160
    by_cases hrneg1 : r = -1
    · have hxlt : x < 10 ^ 18 := by
        exact (lnWadToRayBody_negative_iff h1 h2).mp (by omega)
      simpa [r, hrneg1] using cutLogWadRayLtRational_at_neg_one hxlt
    · by_cases hcgt : 160 < evmClz x
      · by_cases hr0 : 0 ≤ r
        · exact lnWadToRayBody_error_bound_upper_neg_shift_nonneg h1 h2 hwad hcgt hr0
        · have hrle : r ≤ -2 := by omega
          exact lnWadToRayBody_error_bound_upper_neg_shift_rec_ge h1 h2 hwad hcgt hrle
      · have hclt : evmClz x < 160 := by omega
        exact lnWadToRayBody_error_bound_upper_pos_shift h1 h2 hwad hclt

end LnFloorCert

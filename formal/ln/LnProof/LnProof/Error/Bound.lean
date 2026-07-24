import LnProof.Error.Core.Assembly
import LnProof.Error.LtBridge

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

/-!
# Public cut statement for the `lnWadToRay` error bound

The published cut is `1698600000 / 10^9 = 1.6986` ulp.  The positive lt octave
splits at the bracket-validity boundary: the mantissa window `[2^95, Sc-46]`
is covered by the degree-22 curved-cap Kronecker cell cover (`lt_pos_cut_reduced`
fed by `errLt_reduced_ineq`), and the residue band `[Sc-45, Sc)` by the coarse residue
bound (`lo_lt_pos_exact`, whose octave budget binds at `Sc-45`).  The positive
ge octave and the negative shift keep their coarse residue bounds (which already
clear `1.6986`).  The coarse residue predicate holds for every mantissa directly
from the floor bracket `1 ≤ posResidueGap` (`posResidueGap_bounds`).
-/

namespace LnFloorCert

open LnYul LnFloor Common.Exp Common.Poly

attribute [local irreducible] lnWadToRayBody

theorem posPhaseNatLt_cast {m c : Nat}
    (hX : int256 (x1W (zWord m)) ≤ 0)
    (hneg : posNegXNat m ≤ posConstNat c) :
    ((posPhaseNatLt m c : Nat) : Int) =
      posPhaseI m c * (lnErrorBoundDen : Int) := by
  have hconst := posConstNat_cast c
  have hnegc := posNegXNat_cast (m := m) hX
  have hsub : ((posConstNat c - posNegXNat m : Nat) : Int) =
      ((posConstNat c : Nat) : Int) - ((posNegXNat m : Nat) : Int) := by
    omega
  unfold posPhaseNatLt
  rw [hsub, hconst, hnegc]
  unfold posPhaseI
  rw [Int.add_mul, Int.add_mul, Int.add_mul]
  rw [show (-int256 (x1W (zWord m)) * lnPhaseScaleI) *
      (lnErrorBoundDen : Int) =
        -(int256 (x1W (zWord m)) * lnPhaseScaleI * (lnErrorBoundDen : Int)) by
        rw [Int.neg_mul, Int.neg_mul]]
  omega

theorem minPosAvail_cast :
    ((minPosAvail : Nat) : Int) =
      (lnErrorExtraNum : Int) * twoPow99I +
        twoPow27I * (lnErrorBoundDen : Int) := by
  unfold minPosAvail lnPhaseExtraArg twoPow99N twoPow27N twoPow99I twoPow27I
  unfold lnErrorExtraNum lnErrorBoundNum lnErrorBoundDen
  decide +kernel

theorem posPhaseNatLt_minAvail_le_lnErrArg {m c : Nat}
    (hmlo : MLO ≤ m) (hmlt : m < Sc) (hc : c < 160) :
    posPhaseNatLt m c + minPosAvail ≤
      lnErrArg (int256 (lnTail (evmSub 160 c) m)) := by
  let r := int256 (lnTail (evmSub 160 c) m)
  have hmhi : m < MHI := by
    simp only [Sc, MHI] at hmlt ⊢
    omega
  have hX := x1_nonpos_ltF hmlo hmlt
  have hV0 : 0 ≤
      int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c + lnBiasI := by
    simpa [posAccI] using posAccI_nonneg hmlo hmhi hc
  have hneg := posNegXNat_le_posConstNat hX (by omega : c ≤ 160) hV0
  have hgap : 1 ≤ posResidueGap m c r := by
    simpa [r] using (posResidueGap_bounds hmlo hmhi hc).1
  have hdecomp := lnErrArg_eq_posPhase_gap (m := m) (c := c) hmlo hmhi hc
  change ((lnErrArg r : Nat) : Int) =
      posPhaseI m c * (lnErrorBoundDen : Int) +
        (lnErrorExtraNum : Int) * twoPow99I +
          posResidueGap m c r * twoPow27I * (lnErrorBoundDen : Int) at hdecomp
  apply Int.ofNat_le.mp
  rw [Int.natCast_add, posPhaseNatLt_cast hX hneg, minPosAvail_cast, hdecomp]
  have h27 : 0 ≤ twoPow27I := by
    unfold twoPow27I
    decide
  have hden : 0 ≤ (lnErrorBoundDen : Int) := by
    change (0 : Int) ≤ 1000000000
    decide
  have hgap27 :
      1 * twoPow27I ≤ posResidueGap m c r * twoPow27I :=
    Int.mul_le_mul_of_nonneg_right hgap h27
  have hgapDen :
      1 * twoPow27I * (lnErrorBoundDen : Int) ≤
        posResidueGap m c r * twoPow27I * (lnErrorBoundDen : Int) :=
    Int.mul_le_mul_of_nonneg_right hgap27 hden
  have hgapDen' :
      twoPow27I * (lnErrorBoundDen : Int) ≤
        posResidueGap m c r * twoPow27I * (lnErrorBoundDen : Int) := by
    simpa [Int.one_mul] using hgapDen
  have hinner :
      (lnErrorExtraNum : Int) * twoPow99I +
          twoPow27I * (lnErrorBoundDen : Int) ≤
        (lnErrorExtraNum : Int) * twoPow99I +
          posResidueGap m c r * twoPow27I * (lnErrorBoundDen : Int) :=
    Int.add_le_add_left hgapDen' _
  have hmain :
      posPhaseI m c * (lnErrorBoundDen : Int) +
          ((lnErrorExtraNum : Int) * twoPow99I +
            twoPow27I * (lnErrorBoundDen : Int)) ≤
        posPhaseI m c * (lnErrorBoundDen : Int) +
          ((lnErrorExtraNum : Int) * twoPow99I +
            posResidueGap m c r * twoPow27I * (lnErrorBoundDen : Int)) :=
    Int.add_le_add_left hinner _
  simpa [Int.add_assoc] using hmain

/-- Uniform coarse residue (full positive-shift): holds for every mantissa from
the floor bracket because `lnErrorCoarsePosResidue = 0`. -/
theorem PosShiftResidueOk_uniform {m c : Nat} (hmlo : MLO ≤ m) (hmhi : m < MHI)
    (hc : c < 160) :
    PosShiftResidueOk m c (int256 (lnTail (evmSub 160 c) m)) := by
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
    PosShiftGeResidueOk m c (int256 (lnTail (evmSub 160 c) m)) := by
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

theorem lnWadToRayBody_positive_shift_ge_residue_cert {x : Nat}
    (h1 : 1 ≤ x) (h2 : x < 2 ^ 255)
    (hclt : evmClz x < 160) :
    PosShiftGeResidueOk (mant x) (evmClz x) (int256 (lnWadToRayBody x)) := by
  have hx256 : x < 2 ^ 256 := by omega
  have htail :
      lnWadToRayBody x = lnTail (evmSub 160 (evmClz x)) (mant x) := by
    rw [lnWadToRayBody_eq_tail hx256]
    rfl
  obtain ⟨me, hmlo, hmhi⟩ := mant_facts h1 h2
  have hmant_lo : MLO ≤ mant x := by
    unfold mant
    rw [me]
    exact hmlo
  have hmant_hi : mant x < MHI := by
    unfold mant
    rw [me]
    exact hmhi
  rw [htail]
  exact PosShiftGeResidueOk_uniform hmant_lo hmant_hi hclt

theorem lnWadToRayBody_positive_shift_lt_residue_cert {x : Nat}
    (h1 : 1 ≤ x) (h2 : x < 2 ^ 255)
    (hclt : evmClz x < 160) :
    PosShiftResidueOk (mant x) (evmClz x) (int256 (lnWadToRayBody x)) := by
  have hx256 : x < 2 ^ 256 := by omega
  have htail :
      lnWadToRayBody x = lnTail (evmSub 160 (evmClz x)) (mant x) := by
    rw [lnWadToRayBody_eq_tail hx256]
    rfl
  obtain ⟨me, hmlo, hmhi⟩ := mant_facts h1 h2
  have hmant_lo : MLO ≤ mant x := by
    unfold mant
    rw [me]
    exact hmlo
  have hmant_hi : mant x < MHI := by
    unfold mant
    rw [me]
    exact hmhi
  rw [htail]
  exact PosShiftResidueOk_uniform hmant_lo hmant_hi hclt

theorem lnWadToRayBody_error_bound_upper_pos_shift {x : Nat}
    (h1 : 1 ≤ x) (h2 : x < 2 ^ 255) (hne : x ≠ 10 ^ 18)
    (hclt : evmClz x < 160) :
    CutLogWadRayLtRational x (int256 (lnWadToRayBody x)) lnErrorBoundNum lnErrorBoundDen := by
  obtain ⟨me, hmlo, hmhi⟩ := mant_facts h1 h2
  have hmant_eq : mant x = x * 2 ^ (255 - Nat.log2 x) / 2 ^ 160 := me
  have hmant_lo : MLO ≤ mant x := by rw [hmant_eq]; exact hmlo
  have hmant_hi : mant x < MHI := by rw [hmant_eq]; exact hmhi
  obtain ⟨hc1, _hc255⟩ := clz_bounds h1 h2
  have hpos : 1 ≤ int256 (lnWadToRayBody x) * (lnErrorBoundDen : Int) +
      (lnErrorBoundNum : Int) := by
    have hr0 := lnWadToRayBody_nonneg_of_clz_lt_160 h1 h2 hclt
    unfold lnErrorBoundDen lnErrorBoundNum
    omega
  unfold CutLogWadRayLtRational
  rw [if_pos hpos]
  change capLB (lnErrArg (int256 (lnWadToRayBody x))) lnErrQ x (10 ^ 18)
  rcases Nat.lt_or_ge (mant x) Sc with hbranch | hbranch
  · -- positive shift, lt octave: cell cut on `[2^95, Sc-46]`, residue band on `[Sc-45, Sc)`
    rcases Nat.lt_or_ge (mant x) (Sc - 45) with hcell | hband
    · -- cell domain: `mant x < Sc - 45` ⟹ `mant x + 46 ≤ Sc`
      have hx256 : x < 2 ^ 256 := by omega
      have htail : lnWadToRayBody x = lnTail (evmSub 160 (evmClz x)) (mant x) := by
        rw [lnWadToRayBody_eq_tail hx256]; rfl
      have hh2 : mant x + 46 ≤ Sc := by omega
      have hmin : posPhaseNatLt (mant x) (evmClz x) + minPosAvail ≤
          lnErrArg (int256 (lnWadToRayBody x)) := by
        have hp := posPhaseNatLt_minAvail_le_lnErrArg hmant_lo (by omega : mant x < Sc) hclt
        rw [← htail] at hp; exact hp
      have hxtop : x ≤ posTopX (evmClz x) (mant x) := by
        have hw := mant_window_le h1 h2 (by omega : evmClz x ≤ 160)
        have hwpos : 0 < (mant x + 1) * 2 ^ (160 - evmClz x) :=
          Nat.mul_pos (Nat.succ_pos _) (Nat.pow_pos (by decide))
        unfold posTopX; omega
      have hcut := lt_pos_cut_reduced (m := mant x) (c := evmClz x) (x := x)
        (r := int256 (lnWadToRayBody x)) hmant_lo hh2 hc1 hclt hmin hxtop
        (errLt_reduced_ineq hmant_lo hh2)
      refine capLB_weaken (p := lnErrArg (int256 (lnWadToRayBody x))) (q := lnErrQ)
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
      exact lnWadToRayBody_positive_shift_lt_residue h1 h2 hne hclt hbranch hband
        (lnWadToRayBody_positive_shift_lt_residue_cert h1 h2 hclt)
  · exact lnWadToRayBody_positive_shift_ge_residue h1 h2 hclt hbranch
      (lnWadToRayBody_positive_shift_ge_residue_cert h1 h2 hclt)

/-- The body decomposition satisfies the `1.6986` ulp error-bound cut: the lt octave is
covered by the degree-22 curved-cap cell cover on `[2^95, Sc-46]` and a residue
band on `[Sc-45, Sc)`, the ge octave by the coarse residue bound, and the
negative shift by its coarse residue bound. -/
theorem lnWadToRayBody_error_bound_1_6986 {x : Nat} (h1 : 1 ≤ x) (h2 : x < 2 ^ 255) :
    let r := int256 (lnWadToRayBody x)
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
  let r := int256 (lnWadToRayBody x)
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

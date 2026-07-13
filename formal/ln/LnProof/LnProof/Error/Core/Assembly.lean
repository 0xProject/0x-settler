import LnProof.Floor.CutEquiv
import LnProof.Error.Cert
import LnProof.Error.Core.CutDefs
import LnProof.Error.Core.ExpMargin
import LnProof.Error.Core.ResidueCover
import LnProof.Error.Core.Budget
import LnProof.Error.Core.Direct
import LnProof.Error.Core.PhaseCover
import LnProof.Error.Core.Bounds
import LnProof.Error.Core.C160
import LnProof.Error.Core.BranchPos
import LnProof.Error.Core.BranchNeg
import LnProof.Error.Core.BranchBn

/-!
# Error bound — Assembly

Upper-bound assembly: the `lnWadToRayBody_*` positive/negative-shift error-bound theorems that `Error.Bound` consumes.
-/

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

namespace LnFloorCert

open LnYul LnFloor Common.Exp Common.Poly

attribute [local irreducible] lnWadToRayBody


theorem r_nonneg_of_c160_v_nonneg {m : Nat} {R : Int}
    (hV0 : 0 ≤ int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt 160 +
      116873961749927929127912020551516294209054209107914)
    (hr : int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt 160 +
      116873961749927929127912020551516294209054209107914 < (R + 1) * 2 ^ 72) :
    0 ≤ R := by
  rcases Int.lt_or_le R 0 with hneg | hnon
  · exfalso
    have hle : (R + 1) * 2 ^ 72 ≤ 0 := by
      have : R + 1 ≤ 0 := by omega
      exact Int.mul_le_mul_of_nonneg_right this (by decide : (0 : Int) ≤ 2 ^ 72)
    omega
  · exact hnon

theorem wad_le_of_clz_lt_160 {x : Nat} (h1 : 1 ≤ x) (h2 : x < 2 ^ 255)
    (hclt : evmClz x < 160) :
    10 ^ 18 ≤ x := by
  rcases Nat.lt_or_ge x (10 ^ 18) with hxlt | hxge
  · exfalso
    have hclz : evmClz x = 255 - Nat.log2 x := evmClz_eq h1 (by omega)
    have hx60 : x < 2 ^ 60 := by
      have hdec : (10 : Nat) ^ 18 < 2 ^ 60 := by decide
      omega
    have hlog : Nat.log2 x < 60 := (Nat.log2_lt (by omega)).mpr hx60
    have hlog_le : Nat.log2 x ≤ 59 := by omega
    have hclz_ge : 196 ≤ evmClz x := by
      rw [hclz]
      omega
    omega
  · exact hxge

theorem lnWadToRayBody_nonneg_of_clz_lt_160 {x : Nat} (h1 : 1 ≤ x) (h2 : x < 2 ^ 255)
    (hclt : evmClz x < 160) :
    0 ≤ int256 (lnWadToRayBody x) := by
  have hxge := wad_le_of_clz_lt_160 h1 h2 hclt
  rcases Int.lt_or_le (int256 (lnWadToRayBody x)) 0 with hneg | hnon
  · have hxlt := (lnWadToRayBody_negative_iff h1 h2).mp hneg
    omega
  · exact hnon

theorem lnWadToRayBody_error_bound_upper_c160 {x : Nat} (h1 : 1 ≤ x) (h2 : x < 2 ^ 255)
    (hne : x ≠ 10 ^ 18) (hc160 : evmClz x = 160) :
    CutLogWadRayLtRational x (int256 (lnWadToRayBody x)) lnErrorBoundNum lnErrorBoundDen := by
  obtain ⟨hbr1, hbr2⟩ := lnWadToRayBody_floor_bracket h1 h2 hne
  rw [show (4722366482869645213696 : Int) = 2 ^ 72 from by decide] at hbr1 hbr2
  have hbr2' : int256 (x1W (zWord (mant x))) * 7450580596923828125 +
      ln2kInt (evmClz x) + 116873961749927929127912020551516294209054209107914 <
      (int256 (lnWadToRayBody x) + 1) * 2 ^ 72 := by
    have e : (int256 (lnWadToRayBody x) + 1) * 2 ^ 72 =
        int256 (lnWadToRayBody x) * 2 ^ 72 + 2 ^ 72 := by
      rw [Int.add_mul, Int.one_mul]
    omega
  revert hbr1 hbr2'
  generalize int256 (lnWadToRayBody x) = R
  intro hbr1 hbr2'
  obtain ⟨me, hmlo, hmhi⟩ := mant_facts h1 h2
  have hmant_eq : mant x = x * 2 ^ (255 - Nat.log2 x) / 2 ^ 160 := me
  have hmant_lo : MLO ≤ mant x := by rw [hmant_eq]; exact hmlo
  have hmant_hi : mant x < MHI := by rw [hmant_eq]; exact hmhi
  have hc : evmClz x ≤ 160 := by omega
  obtain ⟨hw1, hw2⟩ := mant_window_le h1 h2 hc
  have hw1' : mant x ≤ x := by
    rw [hc160] at hw1
    simpa only [Nat.sub_self, Nat.pow_zero, Nat.mul_one] using hw1
  have hw2' : x < mant x + 1 := by
    rw [hc160] at hw2
    simpa only [Nat.sub_self, Nat.pow_zero, Nat.mul_one] using hw2
  have hbr2c : int256 (x1W (zWord (mant x))) * 7450580596923828125 +
      ln2kInt 160 + 116873961749927929127912020551516294209054209107914 <
      (R + 1) * 2 ^ 72 := by
    simpa [hc160] using hbr2'
  apply CutLogWadRayLtRational_of_strict (by omega)
  unfold CutLogWadRayLtRationalStrict
  rw [if_pos]
  · rcases Nat.lt_or_ge (mant x) Sc with hbranch | hbranch
    · exact lo_lt_c160_exact hmant_lo hbranch hbr2c hw1' hw2'
    · have hV0 := v_pos_ge_pos hbranch hmant_hi (by decide : 160 ≤ 160)
      have hr0 := r_nonneg_of_c160_v_nonneg hV0 hbr2c
      exact lo_ge_c160_exact hbranch hmant_hi hbr2c (by omega) hw1' hw2'
  · rcases Nat.lt_or_ge (mant x) Sc with hbranch | hbranch
    · have hmhi : mant x < MHI := hmant_hi
      have hV0I := v_c160_nonneg hmant_lo hmhi
      have hV0 : 0 ≤ int256 (x1W (zWord (mant x))) * 7450580596923828125 +
          ln2kInt 160 + 116873961749927929127912020551516294209054209107914 := by
        simpa [lnBiasI] using hV0I
      have hr0 := r_nonneg_of_c160_v_nonneg hV0 hbr2c
      unfold lnErrorBoundDen lnErrorBoundNum
      omega
    · have hV0 := v_pos_ge_pos hbranch hmant_hi (by decide : 160 ≤ 160)
      have hr0 := r_nonneg_of_c160_v_nonneg hV0 hbr2c
      unfold lnErrorBoundDen lnErrorBoundNum
      omega

theorem lnWadToRayBody_error_bound_upper_neg_shift_nonneg {x : Nat}
    (h1 : 1 ≤ x) (h2 : x < 2 ^ 255) (hne : x ≠ 10 ^ 18)
    (hcgt : 160 < evmClz x) (hr0 : 0 ≤ int256 (lnWadToRayBody x)) :
    CutLogWadRayLtRational x (int256 (lnWadToRayBody x)) lnErrorBoundNum lnErrorBoundDen := by
  obtain ⟨hbr1, hbr2⟩ := lnWadToRayBody_floor_bracket h1 h2 hne
  rw [show (4722366482869645213696 : Int) = 2 ^ 72 from by decide] at hbr1 hbr2
  have hbr2' : int256 (x1W (zWord (mant x))) * 7450580596923828125 +
      ln2kInt (evmClz x) + 116873961749927929127912020551516294209054209107914 <
      (int256 (lnWadToRayBody x) + 1) * 2 ^ 72 := by
    have e : (int256 (lnWadToRayBody x) + 1) * 2 ^ 72 =
        int256 (lnWadToRayBody x) * 2 ^ 72 + 2 ^ 72 := by
      rw [Int.add_mul, Int.one_mul]
    omega
  revert hbr1 hbr2' hr0
  generalize int256 (lnWadToRayBody x) = R
  intro hr0 hbrLo hbrHi
  obtain ⟨me, hmlo, hmhi⟩ := mant_facts h1 h2
  have hmant_eq : mant x = x * 2 ^ (255 - Nat.log2 x) / 2 ^ 160 := me
  have hmant_lo : MLO ≤ mant x := by rw [hmant_eq]; exact hmlo
  have hmant_hi : mant x < MHI := by rw [hmant_eq]; exact hmhi
  obtain ⟨_hc1, hc255⟩ := clz_bounds h1 h2
  have hw := mant_window_gt h1 h2 hcgt
  have hpos : 1 ≤ R * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int) := by
    unfold lnErrorBoundDen lnErrorBoundNum
    omega
  apply CutLogWadRayLtRational_of_strict (by omega)
  unfold CutLogWadRayLtRationalStrict
  rw [if_pos hpos]
  change capLB (lnErrArg R) lnErrQ (wadRayNum x) wadRayStrictDen
  rcases Nat.lt_or_ge (mant x) Sc with hbranch | hbranch
  · exact lo_lt_neg_exact hmant_lo hbranch hcgt hc255 hbrHi hbrLo hr0 hw
  · exact lo_ge_neg_exact hbranch hmant_hi hcgt hc255 hbrHi hbrLo hr0 hw

theorem lnWadToRayBody_error_bound_upper_neg_shift_rec_ge {x : Nat}
    (h1 : 1 ≤ x) (h2 : x < 2 ^ 255) (hne : x ≠ 10 ^ 18)
    (hcgt : 160 < evmClz x) (hrneg : int256 (lnWadToRayBody x) ≤ -2) :
    CutLogWadRayLtRational x (int256 (lnWadToRayBody x)) lnErrorBoundNum lnErrorBoundDen := by
  obtain ⟨_hbr1, hbr2⟩ := lnWadToRayBody_floor_bracket h1 h2 hne
  rw [show (4722366482869645213696 : Int) = 2 ^ 72 from by decide] at hbr2
  have hbrHi : int256 (x1W (zWord (mant x))) * 7450580596923828125 +
      ln2kInt (evmClz x) + 116873961749927929127912020551516294209054209107914 <
      (int256 (lnWadToRayBody x) + 1) * 2 ^ 72 := by
    have e : (int256 (lnWadToRayBody x) + 1) * 2 ^ 72 =
        int256 (lnWadToRayBody x) * 2 ^ 72 + 2 ^ 72 := by
      rw [Int.add_mul, Int.one_mul]
    omega
  revert hbrHi hrneg
  generalize int256 (lnWadToRayBody x) = R
  intro hrneg hbrHi
  obtain ⟨me, hmlo, hmhi⟩ := mant_facts h1 h2
  have hmant_eq : mant x = x * 2 ^ (255 - Nat.log2 x) / 2 ^ 160 := me
  have hmant_lo : MLO ≤ mant x := by rw [hmant_eq]; exact hmlo
  have hmant_hi : mant x < MHI := by rw [hmant_eq]; exact hmhi
  obtain ⟨_hc1, hc255⟩ := clz_bounds h1 h2
  have hw := mant_window_gt h1 h2 hcgt
  have hneg : ¬1 ≤ R * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int) := by
    unfold lnErrorBoundDen lnErrorBoundNum
    omega
  apply CutLogWadRayLtRational_of_strict (by omega)
  unfold CutLogWadRayLtRationalStrict
  rw [if_neg hneg]
  change capUB (lnErrNegArg R) lnErrQ wadRayStrictDen (wadRayNum x)
  rcases Nat.lt_or_ge (mant x) Sc with hbranch | hbranch
  · exact bn_lt_neg_exact hmant_lo hbranch hcgt hc255 hbrHi hrneg hw
  · exact bn_ge_neg_exact hbranch hmant_hi hcgt hc255 hbrHi hrneg hw

theorem lnWadToRayBody_positive_shift_ge_top_or_direct {x : Nat}
    (h1 : 1 ≤ x) (h2 : x < 2 ^ 255) (hne : x ≠ 10 ^ 18)
    (hclt : evmClz x < 160) (hge : Sc ≤ mant x)
    (hcert : PosShiftGeTopBudgetIneqOk (mant x) (evmClz x) ∨
      PosShiftTopDirectOk 320 (mant x) (evmClz x)) :
    capLB (lnErrArg (int256 (lnWadToRayBody x))) lnErrQ x (10 ^ 18) := by
  have hx256 : x < 2 ^ 256 := by omega
  have htail :
      lnWadToRayBody x = lnTail (evmSub 160 (evmClz x)) (mant x) := by
    rw [lnWadToRayBody_eq_tail hx256]
    rfl
  rcases hcert with htopBudget | hdirect
  · have htop : x ≤ posTopX (evmClz x) (mant x) := by
      have hw := mant_window_le h1 h2 (by omega : evmClz x ≤ 160)
      have hpos : 0 < (mant x + 1) * 2 ^ (160 - evmClz x) :=
        Nat.mul_pos (Nat.succ_pos _) (Nat.pow_pos (by decide))
      unfold posTopX
      omega
    obtain ⟨_hbr1, hbr2⟩ := lnWadToRayBody_floor_bracket h1 h2 hne
    rw [show (4722366482869645213696 : Int) = 2 ^ 72 from by decide] at hbr2
    have hbrHi : int256 (x1W (zWord (mant x))) * 7450580596923828125 +
        ln2kInt (evmClz x) + lnBiasI <
        (int256 (lnWadToRayBody x) + 1) * 2 ^ 72 := by
      have e : (int256 (lnWadToRayBody x) + 1) * 2 ^ 72 =
          int256 (lnWadToRayBody x) * 2 ^ 72 + 2 ^ 72 := by
        rw [Int.add_mul, Int.one_mul]
      rw [e]
      simpa [lnBiasI] using hbr2
    obtain ⟨me, _hmlo, hmhi⟩ := mant_facts h1 h2
    have hmant_hi : mant x < MHI := by
      unfold mant
      rw [me]
      exact hmhi
    have hr0 := lnWadToRayBody_nonneg_of_clz_lt_160 h1 h2 hclt
    have hphase :
        posPhaseNatGe (mant x) (evmClz x) ≤ lnErrArg (int256 (lnWadToRayBody x)) :=
      posPhaseNatGe_le_lnErrArg hge hmant_hi (by omega) hbrHi (by omega)
    have hineq : PosShiftGeBudgetIneqOk (mant x) (evmClz x) x
        (int256 (lnWadToRayBody x)) := by
      change PosShiftGeBudgetIneqOk (mant x) (evmClz x)
        (posTopX (evmClz x) (mant x)) (int256 (lnTail (evmSub 160 (evmClz x)) (mant x))) at htopBudget
      rw [← htail] at htopBudget
      unfold PosShiftGeBudgetIneqOk at htopBudget ⊢
      have hnum : wadRayNum x ≤ wadRayNum (posTopX (evmClz x) (mant x)) := by
        unfold wadRayNum
        exact Nat.mul_le_mul_right (10 ^ 31) htop
      exact Nat.le_trans (Nat.mul_le_mul_right (posBaseWGe (evmClz x) * lnErrQ) hnum)
        htopBudget
    exact capLB_strict_to_exact
      (lo_ge_pos_budget_exact hge hmant_hi hclt ⟨hphase, hineq⟩)
  · unfold PosShiftTopDirectOk at hdirect
    exact pos_shift_direct_exact_of_sumGE h1 h2 hclt hdirect

theorem lnWadToRayBody_positive_shift_lt_top_or_direct {x : Nat}
    (h1 : 1 ≤ x) (h2 : x < 2 ^ 255) (hne : x ≠ 10 ^ 18)
    (hclt : evmClz x < 160) (hlt : mant x < Sc)
    (hcert : PosShiftLtTopBudgetIneqOk (mant x) (evmClz x) ∨
      PosShiftTopDirectOk 320 (mant x) (evmClz x)) :
    capLB (lnErrArg (int256 (lnWadToRayBody x))) lnErrQ x (10 ^ 18) := by
  have hx256 : x < 2 ^ 256 := by omega
  have htail :
      lnWadToRayBody x = lnTail (evmSub 160 (evmClz x)) (mant x) := by
    rw [lnWadToRayBody_eq_tail hx256]
    rfl
  rcases hcert with htopBudget | hdirect
  · have htop : x ≤ posTopX (evmClz x) (mant x) := by
      have hw := mant_window_le h1 h2 (by omega : evmClz x ≤ 160)
      have hpos : 0 < (mant x + 1) * 2 ^ (160 - evmClz x) :=
        Nat.mul_pos (Nat.succ_pos _) (Nat.pow_pos (by decide))
      unfold posTopX
      omega
    obtain ⟨hbr1, hbr2⟩ := lnWadToRayBody_floor_bracket h1 h2 hne
    rw [show (4722366482869645213696 : Int) = 2 ^ 72 from by decide] at hbr1 hbr2
    have hbrHi : int256 (x1W (zWord (mant x))) * 7450580596923828125 +
        ln2kInt (evmClz x) + lnBiasI <
        (int256 (lnWadToRayBody x) + 1) * 2 ^ 72 := by
      have e : (int256 (lnWadToRayBody x) + 1) * 2 ^ 72 =
          int256 (lnWadToRayBody x) * 2 ^ 72 + 2 ^ 72 := by
        rw [Int.add_mul, Int.one_mul]
      rw [e]
      simpa [lnBiasI] using hbr2
    obtain ⟨me, hmlo, _hmhi⟩ := mant_facts h1 h2
    have hmant_lo : MLO ≤ mant x := by
      unfold mant
      rw [me]
      exact hmlo
    have hX := x1_nonpos_ltF hmant_lo hlt
    have hr0 := lnWadToRayBody_nonneg_of_clz_lt_160 h1 h2 hclt
    have hV0 : 0 ≤ int256 (x1W (zWord (mant x))) * 7450580596923828125 +
        ln2kInt (evmClz x) + lnBiasI := by
      have hR0 : 0 ≤ int256 (lnWadToRayBody x) * 2 ^ 72 :=
        Int.mul_nonneg hr0 (by decide)
      have h := Int.le_trans hR0 hbr1
      simpa [lnBiasI] using h
    have hneg := posNegXNat_le_posConstNat hX (by omega) hV0
    have hphase :
        posPhaseNatLt (mant x) (evmClz x) ≤ lnErrArg (int256 (lnWadToRayBody x)) :=
      posPhaseNatLt_le_lnErrArg hX (by omega) hneg hbrHi (by omega)
    have hineq : PosShiftLtBudgetIneqOk (mant x) (evmClz x) x
        (int256 (lnWadToRayBody x)) := by
      change PosShiftLtBudgetIneqOk (mant x) (evmClz x)
        (posTopX (evmClz x) (mant x)) (int256 (lnTail (evmSub 160 (evmClz x)) (mant x))) at htopBudget
      rw [← htail] at htopBudget
      unfold PosShiftLtBudgetIneqOk at htopBudget ⊢
      have hnum : wadRayNum x ≤ wadRayNum (posTopX (evmClz x) (mant x)) := by
        unfold wadRayNum
        exact Nat.mul_le_mul_right (10 ^ 31) htop
      exact Nat.le_trans (Nat.mul_le_mul_right (posBaseWLt (evmClz x) * lnErrQ) hnum)
        htopBudget
    exact capLB_strict_to_exact
      (lo_lt_pos_budget_exact hmant_lo hlt hclt ⟨hneg, hphase, hineq⟩)
  · unfold PosShiftTopDirectOk at hdirect
    exact pos_shift_direct_exact_of_sumGE h1 h2 hclt hdirect

theorem lnWadToRayBody_positive_shift_ge_residue_or_direct {x : Nat}
    (h1 : 1 ≤ x) (h2 : x < 2 ^ 255)
    (hclt : evmClz x < 160) (hge : Sc ≤ mant x)
    (hcert : PosShiftGeResidueOk (mant x) (evmClz x) (int256 (lnWadToRayBody x)) ∨
      PosShiftTopDirectOk 320 (mant x) (evmClz x)) :
    capLB (lnErrArg (int256 (lnWadToRayBody x))) lnErrQ x (10 ^ 18) := by
  rcases hcert with hres | hdirect
  · obtain ⟨_me, _hmlo, hmhi⟩ := mant_facts h1 h2
    have hmant_hi : mant x < MHI := by
      unfold mant
      rw [_me]
      exact hmhi
    obtain ⟨hc1, _hc255⟩ := clz_bounds h1 h2
    obtain ⟨_hw1, hw2⟩ := mant_window_le h1 h2 (by omega : evmClz x ≤ 160)
    have hr0 := lnWadToRayBody_nonneg_of_clz_lt_160 h1 h2 hclt
    exact capLB_strict_to_exact
      (lo_ge_pos_exact_ge_residue hge hmant_hi hc1 hclt hr0 hres hw2)
  · unfold PosShiftTopDirectOk at hdirect
    exact pos_shift_direct_exact_of_sumGE h1 h2 hclt hdirect

theorem lnWadToRayBody_positive_shift_lt_residue_or_direct {x : Nat}
    (h1 : 1 ≤ x) (h2 : x < 2 ^ 255) (hne : x ≠ 10 ^ 18)
    (hclt : evmClz x < 160) (hlt : mant x < Sc) (hband_lo : Sc - 45 ≤ mant x)
    (hcert : PosShiftResidueOk (mant x) (evmClz x) (int256 (lnWadToRayBody x)) ∨
      PosShiftTopDirectOk 320 (mant x) (evmClz x)) :
    capLB (lnErrArg (int256 (lnWadToRayBody x))) lnErrQ x (10 ^ 18) := by
  rcases hcert with hres | hdirect
  · obtain ⟨hbr1, _hbr2⟩ := lnWadToRayBody_floor_bracket h1 h2 hne
    rw [show (4722366482869645213696 : Int) = 2 ^ 72 from by decide] at hbr1
    obtain ⟨hc1, _hc255⟩ := clz_bounds h1 h2
    obtain ⟨_hw1, hw2⟩ := mant_window_le h1 h2 (by omega : evmClz x ≤ 160)
    have hr0 := lnWadToRayBody_nonneg_of_clz_lt_160 h1 h2 hclt
    exact capLB_strict_to_exact
      (lo_lt_pos_exact hband_lo hlt hc1 hclt hbr1 hr0 hres hw2)
  · unfold PosShiftTopDirectOk at hdirect
    exact pos_shift_direct_exact_of_sumGE h1 h2 hclt hdirect

theorem lnWadToRayBody_positive_shift_ge_phase_direct {x : Nat}
    (h1 : 1 ≤ x) (h2 : x < 2 ^ 255) (hne : x ≠ 10 ^ 18)
    (hclt : evmClz x < 160) (hge : Sc ≤ mant x)
    (hcert : PosShiftGePhaseDirectOk 320 (mant x) (evmClz x)) :
    capLB (lnErrArg (int256 (lnWadToRayBody x))) lnErrQ x (10 ^ 18) := by
  obtain ⟨_hbr1, hbr2⟩ := lnWadToRayBody_floor_bracket h1 h2 hne
  rw [show (4722366482869645213696 : Int) = 2 ^ 72 from by decide] at hbr2
  have hbrHi : int256 (x1W (zWord (mant x))) * 7450580596923828125 +
      ln2kInt (evmClz x) + lnBiasI <
      (int256 (lnWadToRayBody x) + 1) * 2 ^ 72 := by
    have e : (int256 (lnWadToRayBody x) + 1) * 2 ^ 72 =
        int256 (lnWadToRayBody x) * 2 ^ 72 + 2 ^ 72 := by
      rw [Int.add_mul, Int.one_mul]
    rw [e]
    simpa [lnBiasI] using hbr2
  obtain ⟨me, _hmlo, hmhi⟩ := mant_facts h1 h2
  have hmant_hi : mant x < MHI := by
    unfold mant
    rw [me]
    exact hmhi
  have hr0 := lnWadToRayBody_nonneg_of_clz_lt_160 h1 h2 hclt
  have hp := posPhaseNatGe_extra_le_lnErrArg hge hmant_hi (by omega) hbrHi (by omega)
  have cap0 : capLB (posPhaseNatGe (mant x) (evmClz x) + lnPhaseExtraArg)
      lnErrQ (posTopX (evmClz x) (mant x)) (10 ^ 18) := by
    unfold PosShiftGePhaseDirectOk at hcert
    exact ⟨320, hcert⟩
  have capR : capLB (lnErrArg (int256 (lnWadToRayBody x))) lnErrQ
      (posTopX (evmClz x) (mant x)) (10 ^ 18) := by
    refine capLB_arg (q' := lnErrQ) (by unfold lnErrQ; decide) ?_ cap0
    exact Nat.mul_le_mul_right lnErrQ hp
  have htop : x ≤ posTopX (evmClz x) (mant x) := by
    have hw := mant_window_le h1 h2 (by omega : evmClz x ≤ 160)
    have hpos : 0 < (mant x + 1) * 2 ^ (160 - evmClz x) :=
      Nat.mul_pos (Nat.succ_pos _) (Nat.pow_pos (by decide))
    unfold posTopX
    omega
  refine capLB_weaken (p := lnErrArg (int256 (lnWadToRayBody x))) (q := lnErrQ)
    (y := posTopX (evmClz x) (mant x)) (w := 10 ^ 18)
    (y' := x) (w' := 10 ^ 18) (by decide) capR ?_
  exact Nat.mul_le_mul_right (10 ^ 18) htop

theorem lnWadToRayBody_positive_shift_lt_phase_direct {x : Nat}
    (h1 : 1 ≤ x) (h2 : x < 2 ^ 255) (hne : x ≠ 10 ^ 18)
    (hclt : evmClz x < 160) (hlt : mant x < Sc)
    (hcert : PosShiftLtPhaseDirectOk 320 (mant x) (evmClz x)) :
    capLB (lnErrArg (int256 (lnWadToRayBody x))) lnErrQ x (10 ^ 18) := by
  obtain ⟨hbr1, hbr2⟩ := lnWadToRayBody_floor_bracket h1 h2 hne
  rw [show (4722366482869645213696 : Int) = 2 ^ 72 from by decide] at hbr1 hbr2
  have hbrHi : int256 (x1W (zWord (mant x))) * 7450580596923828125 +
      ln2kInt (evmClz x) + lnBiasI <
      (int256 (lnWadToRayBody x) + 1) * 2 ^ 72 := by
    have e : (int256 (lnWadToRayBody x) + 1) * 2 ^ 72 =
        int256 (lnWadToRayBody x) * 2 ^ 72 + 2 ^ 72 := by
      rw [Int.add_mul, Int.one_mul]
    rw [e]
    simpa [lnBiasI] using hbr2
  obtain ⟨me, hmlo, _hmhi⟩ := mant_facts h1 h2
  have hmant_lo : MLO ≤ mant x := by
    unfold mant
    rw [me]
    exact hmlo
  have hX := x1_nonpos_ltF hmant_lo hlt
  have hr0 := lnWadToRayBody_nonneg_of_clz_lt_160 h1 h2 hclt
  have hV0 : 0 ≤ int256 (x1W (zWord (mant x))) * 7450580596923828125 +
      ln2kInt (evmClz x) + lnBiasI := by
    have hR0 : 0 ≤ int256 (lnWadToRayBody x) * 2 ^ 72 :=
      Int.mul_nonneg hr0 (by decide)
    have h := Int.le_trans hR0 hbr1
    simpa [lnBiasI] using h
  have hneg := posNegXNat_le_posConstNat hX (by omega) hV0
  have hp := posPhaseNatLt_extra_le_lnErrArg hX (by omega) hneg hbrHi (by omega)
  have cap0 : capLB (posPhaseNatLt (mant x) (evmClz x) + lnPhaseExtraArg)
      lnErrQ (posTopX (evmClz x) (mant x)) (10 ^ 18) := by
    unfold PosShiftLtPhaseDirectOk at hcert
    exact ⟨320, hcert⟩
  have capR : capLB (lnErrArg (int256 (lnWadToRayBody x))) lnErrQ
      (posTopX (evmClz x) (mant x)) (10 ^ 18) := by
    refine capLB_arg (q' := lnErrQ) (by unfold lnErrQ; decide) ?_ cap0
    exact Nat.mul_le_mul_right lnErrQ hp
  have htop : x ≤ posTopX (evmClz x) (mant x) := by
    have hw := mant_window_le h1 h2 (by omega : evmClz x ≤ 160)
    have hpos : 0 < (mant x + 1) * 2 ^ (160 - evmClz x) :=
      Nat.mul_pos (Nat.succ_pos _) (Nat.pow_pos (by decide))
    unfold posTopX
    omega
  refine capLB_weaken (p := lnErrArg (int256 (lnWadToRayBody x))) (q := lnErrQ)
    (y := posTopX (evmClz x) (mant x)) (w := 10 ^ 18)
    (y' := x) (w' := 10 ^ 18) (by decide) capR ?_
  exact Nat.mul_le_mul_right (10 ^ 18) htop

theorem lnWadToRayBody_positive_shift_ge_min_phase_direct {x : Nat}
    (h1 : 1 ≤ x) (h2 : x < 2 ^ 255)
    (hclt : evmClz x < 160) (hge : Sc ≤ mant x)
    (hcert : PosShiftGeMinPhaseDirectOk 320 (mant x) (evmClz x)) :
    capLB (lnErrArg (int256 (lnWadToRayBody x))) lnErrQ x (10 ^ 18) := by
  have hx256 : x < 2 ^ 256 := by omega
  have htail :
      lnWadToRayBody x = lnTail (evmSub 160 (evmClz x)) (mant x) := by
    rw [lnWadToRayBody_eq_tail hx256]
    rfl
  obtain ⟨me, _hmlo, hmhi⟩ := mant_facts h1 h2
  have hmant_hi : mant x < MHI := by
    unfold mant
    rw [me]
    exact hmhi
  have hp := posPhaseNatGe_minAvail_le_lnErrArg hge hmant_hi hclt
  rw [← htail] at hp
  have cap0 : capLB (posPhaseNatGe (mant x) (evmClz x) + minPosAvail)
      lnErrQ (posTopX (evmClz x) (mant x)) (10 ^ 18) := by
    unfold PosShiftGeMinPhaseDirectOk at hcert
    exact ⟨320, hcert⟩
  have capR : capLB (lnErrArg (int256 (lnWadToRayBody x))) lnErrQ
      (posTopX (evmClz x) (mant x)) (10 ^ 18) := by
    refine capLB_arg (q' := lnErrQ) (by unfold lnErrQ; decide) ?_ cap0
    exact Nat.mul_le_mul_right lnErrQ hp
  have htop : x ≤ posTopX (evmClz x) (mant x) := by
    have hw := mant_window_le h1 h2 (by omega : evmClz x ≤ 160)
    have hpos : 0 < (mant x + 1) * 2 ^ (160 - evmClz x) :=
      Nat.mul_pos (Nat.succ_pos _) (Nat.pow_pos (by decide))
    unfold posTopX
    omega
  refine capLB_weaken (p := lnErrArg (int256 (lnWadToRayBody x))) (q := lnErrQ)
    (y := posTopX (evmClz x) (mant x)) (w := 10 ^ 18)
    (y' := x) (w' := 10 ^ 18) (by decide) capR ?_
  exact Nat.mul_le_mul_right (10 ^ 18) htop

theorem lnWadToRayBody_positive_shift_lt_min_phase_direct {x : Nat}
    (h1 : 1 ≤ x) (h2 : x < 2 ^ 255)
    (hclt : evmClz x < 160) (hlt : mant x < Sc)
    (hcert : PosShiftLtMinPhaseDirectOk 320 (mant x) (evmClz x)) :
    capLB (lnErrArg (int256 (lnWadToRayBody x))) lnErrQ x (10 ^ 18) := by
  have hx256 : x < 2 ^ 256 := by omega
  have htail :
      lnWadToRayBody x = lnTail (evmSub 160 (evmClz x)) (mant x) := by
    rw [lnWadToRayBody_eq_tail hx256]
    rfl
  obtain ⟨me, hmlo, _hmhi⟩ := mant_facts h1 h2
  have hmant_lo : MLO ≤ mant x := by
    unfold mant
    rw [me]
    exact hmlo
  have hp := posPhaseNatLt_minAvail_le_lnErrArg hmant_lo hlt hclt
  rw [← htail] at hp
  have cap0 : capLB (posPhaseNatLt (mant x) (evmClz x) + minPosAvail)
      lnErrQ (posTopX (evmClz x) (mant x)) (10 ^ 18) := by
    unfold PosShiftLtMinPhaseDirectOk at hcert
    exact ⟨320, hcert⟩
  have capR : capLB (lnErrArg (int256 (lnWadToRayBody x))) lnErrQ
      (posTopX (evmClz x) (mant x)) (10 ^ 18) := by
    refine capLB_arg (q' := lnErrQ) (by unfold lnErrQ; decide) ?_ cap0
    exact Nat.mul_le_mul_right lnErrQ hp
  have htop : x ≤ posTopX (evmClz x) (mant x) := by
    have hw := mant_window_le h1 h2 (by omega : evmClz x ≤ 160)
    have hpos : 0 < (mant x + 1) * 2 ^ (160 - evmClz x) :=
      Nat.mul_pos (Nat.succ_pos _) (Nat.pow_pos (by decide))
    unfold posTopX
    omega
  refine capLB_weaken (p := lnErrArg (int256 (lnWadToRayBody x))) (q := lnErrQ)
    (y := posTopX (evmClz x) (mant x)) (w := 10 ^ 18)
    (y' := x) (w' := 10 ^ 18) (by decide) capR ?_
  exact Nat.mul_le_mul_right (10 ^ 18) htop

end LnFloorCert

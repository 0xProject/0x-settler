import LnProof.Floor.CutEquiv
import LnProof.Error.Cert
import LnProof.Error.Core.CutDefs

/-!
# Error bound — Residue

`posAccI` / `posResidueGap` and the positive-tail floor decomposition.
-/

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

namespace LnFloorCert

open LnYul LnFloor Common.Exp Common.Poly

attribute [local irreducible] lnWadToRayBody


def posPhaseI (m c : Nat) : Int :=
  int256 (x1W (zWord m)) * lnPhaseScaleI +
    ((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I) +
      lnBiasI * twoPow27I

def posAccI (m c : Nat) : Int :=
  int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c + lnBiasI

def posResidueGap (m c : Nat) (r : Int) : Int :=
  (r + 1) * twoPow72I - posAccI m c

theorem posAccI_nonneg {m c : Nat}
    (hmlo : MLO ≤ m) (hmhi : m < MHI) (hc : c < 160) :
    0 ≤ posAccI m c := by
  have hb := (LnYul.r1_bound hmlo hmhi).1
  have hx1 :
      -(240000000000000000000000000000 : Int) * 7450580596923828125 ≤
        int256 (x1W (zWord m)) * 7450580596923828125 :=
    Int.mul_le_mul_of_nonneg_right hb (by decide)
  have hln2 : (LN2c : Int) ≤ ln2kInt c := by
    unfold ln2kInt
    rw [if_pos (by omega : c ≤ 160)]
    have hk : (1 : Int) ≤ ((160 - c : Nat) : Int) := by
      omega
    have hmul : (LN2c : Int) * 1 ≤ (LN2c : Int) * ((160 - c : Nat) : Int) :=
      Int.mul_le_mul_of_nonneg_left hk (by unfold LN2c; decide)
    simpa [Int.mul_one] using hmul
  have hfloor :
      0 ≤
        (-(240000000000000000000000000000 : Int)) *
          7450580596923828125 + (LN2c : Int) + lnBiasI := by
    unfold LN2c lnBiasI
    decide
  unfold posAccI
  omega

theorem lnTail_floor_bracket_pos {m c : Nat}
    (hmlo : MLO ≤ m) (hmhi : m < MHI) (hc : c < 160) :
    let r := int256 (lnTail (evmSub 160 c) m)
    r * twoPow72I ≤ posAccI m c ∧ posAccI m c < (r + 1) * twoPow72I := by
  have hc256 : c < 256 := by omega
  have hacc := r4_value hmlo hmhi hc256
  let s := evmSar 72
    (evmAdd (evmAdd (evmMul (x1W (zWord m)) Kc) (evmMul LN2c (evmSub 160 c))) BIASc)
  have hs := evmSar_sandwich_72 (evmAdd_lt
    (evmAdd (evmMul (x1W (zWord m)) Kc) (evmMul LN2c (evmSub 160 c))) BIASc)
  have hslt : s < 2 ^ 256 := by
    unfold s
    exact hs.1
  have hnon := posAccI_nonneg hmlo hmhi hc
  have hcorr : int256 (lnTail (evmSub 160 c) m) = int256 s := by
    unfold lnTail
    change int256 (evmAdd (evmIszero (evmNot s)) s) = int256 s
    rw [corr_toInt hslt]
    rw [if_neg]
    intro hsneg
    have hhi := hs.2.2
    rw [hacc] at hhi
    change posAccI m c < int256 s * 4722366482869645213696 +
      4722366482869645213696 at hhi
    rw [hsneg] at hhi
    omega
  rw [hcorr]
  have hlo := hs.2.1
  have hhi := hs.2.2
  rw [hacc] at hlo hhi
  change int256 s * 4722366482869645213696 ≤ posAccI m c at hlo
  change posAccI m c < int256 s * 4722366482869645213696 +
    4722366482869645213696 at hhi
  have hpow : twoPow72I = (4722366482869645213696 : Int) := by
    unfold twoPow72I
    decide
  rw [hpow]
  have heq : (int256 s + 1) * (4722366482869645213696 : Int) =
      int256 s * 4722366482869645213696 + 4722366482869645213696 := by
    rw [Int.add_mul, Int.one_mul]
  change int256 s * (4722366482869645213696 : Int) ≤ posAccI m c ∧
    posAccI m c < (int256 s + 1) * (4722366482869645213696 : Int)
  rw [heq]
  exact ⟨hlo, hhi⟩

theorem lnTail_nonneg_pos {m c : Nat}
    (hmlo : MLO ≤ m) (hmhi : m < MHI) (hc : c < 160) :
    0 ≤ int256 (lnTail (evmSub 160 c) m) := by
  have hbr := lnTail_floor_bracket_pos hmlo hmhi hc
  have hnon := posAccI_nonneg hmlo hmhi hc
  unfold twoPow72I at hbr
  omega

theorem posResidueGap_bounds {m c : Nat}
    (hmlo : MLO ≤ m) (hmhi : m < MHI) (hc : c < 160) :
    let r := int256 (lnTail (evmSub 160 c) m)
    1 ≤ posResidueGap m c r ∧ posResidueGap m c r ≤ twoPow72I := by
  have hbr := lnTail_floor_bracket_pos hmlo hmhi hc
  unfold posResidueGap
  have hpow : twoPow72I = (4722366482869645213696 : Int) := by
    unfold twoPow72I
    decide
  rw [hpow] at hbr ⊢
  omega

theorem lnErrArg_eq_posPhase_gap {m c : Nat}
    (hmlo : MLO ≤ m) (hmhi : m < MHI) (hc : c < 160) :
    let r := int256 (lnTail (evmSub 160 c) m)
    ((lnErrArg r : Nat) : Int) =
      posPhaseI m c * (lnErrorBoundDen : Int) +
        (lnErrorExtraNum : Int) * twoPow99I +
          posResidueGap m c r * twoPow27I * (lnErrorBoundDen : Int) := by
  intro r
  have hr0 : 0 ≤ r := lnTail_nonneg_pos hmlo hmhi hc
  have harg : 0 ≤ r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int) := by
    unfold lnErrorBoundDen lnErrorBoundNum
    omega
  have hVs := v_scale_pos (int256 (x1W (zWord m))) c (by omega : c ≤ 160)
  have hVs' : posAccI m c * twoPow27I = posPhaseI m c := by
    unfold posAccI posPhaseI
    simpa [twoPow27I, lnPhaseScaleI, lnBiasI] using hVs
  have hden : ((lnErrorBoundDen : Nat) : Int) = (1000000000 : Int) := by
    unfold lnErrorBoundDen
    rfl
  have hnum : ((lnErrorBoundNum : Nat) : Int) = (1698600000 : Int) := by
    unfold lnErrorBoundNum
    rfl
  have hextra : ((lnErrorExtraNum : Nat) : Int) = (698600000 : Int) := by
    unfold lnErrorExtraNum lnErrorBoundNum lnErrorBoundDen
    decide +kernel
  unfold lnErrArg posResidueGap
  rw [Int.natCast_mul, Int.toNat_of_nonneg harg]
  rw [hden, hnum, hextra]
  unfold twoPow99I twoPow27I at hVs' ⊢
  unfold twoPow72I
  rw [← hVs']
  change (r * 1000000000 + 1698600000) * 633825300114114700748351602688 =
    posAccI m c * 134217728 * 1000000000 +
      698600000 * 633825300114114700748351602688 +
        ((r + 1) * 4722366482869645213696 - posAccI m c) * 134217728 *
          1000000000
  have hP : (4722366482869645213696 : Int) * 134217728 =
      633825300114114700748351602688 := by
    decide
  have hN : (1698600000 : Int) = 1000000000 + 698600000 := by
    decide
  rw [hN, ← hP]
  simp only [Int.add_mul, Int.mul_add, Int.add_assoc, Int.sub_eq_add_neg,
    Int.neg_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  generalize r * (134217728 * (1000000000 * 4722366482869645213696)) = X
  generalize 134217728 * (1000000000 * 4722366482869645213696) = Y
  generalize 134217728 * (698600000 * 4722366482869645213696) = Z
  generalize posAccI m c * (134217728 * 1000000000) = W
  omega

end LnFloorCert

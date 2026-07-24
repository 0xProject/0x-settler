import Common.Seam.RealExpBridge
import LnProof.Model.Body
import LnProof.Spec.Cut

namespace LnFloorCarry

open Common.Exp Common.RealExpBridge LnFloor LnYul

set_option maxRecDepth 100000

noncomputable section

def phaseErrorNum : Nat := 24536250781840436
def phaseErrorDen : Nat := 10 ^ 39
def coreErrorNum : Nat := 32886404036042980977667
def coreErrorDen : Nat := 10 ^ 23
def globalErrorNum : Nat := 3288640403604298097806
def globalErrorDen : Nat := 10 ^ 22

def ln2Word : Real := (LN2c : Real) * 2 ^ 27 / QS
def phaseDeltaRay : Real := 10 ^ 27 * (ln2Word - Real.log 2)
def phaseErrorRay (k : Int) : Real := (k : Real) * phaseDeltaRay
def biasNatural : Real := (BIASc : Real) / (10 ^ 27 * 2 ^ 72)

theorem ln2WordAboveExactCap : capLB (LN2c * 2 ^ 27) QS 2 1 := by
  refine ⟨40, ?_⟩
  decide

theorem ln2WordMinusPhaseCap :
    capUB
      (LN2c * 2 ^ 27 * phaseErrorDen - phaseErrorNum * 2 ^ 99)
      (QS * phaseErrorDen) 2 1 := by
  refine capUB_of_partial (K := 130)
    (by unfold phaseErrorDen QS; decide) (by decide) ?_
  decide

theorem phaseDeltaRay_nonneg : 0 ≤ phaseDeltaRay := by
  have hexp := le_exp_of_capLB
    (p := LN2c * 2 ^ 27) (q := QS) (y := 2) (w := 1)
    QS_pos (by decide) ln2WordAboveExactCap
  have hlog : Real.log 2 ≤ ln2Word := by
    apply (Real.log_le_iff_le_exp (by norm_num : (0 : Real) < 2)).2
    norm_num [ln2Word] at hexp ⊢
    exact hexp
  unfold phaseDeltaRay
  exact mul_nonneg (by positivity) (sub_nonneg.mpr hlog)

theorem phaseDeltaRay_le :
    phaseDeltaRay ≤ (phaseErrorNum : Real) / phaseErrorDen := by
  have hexp := exp_le_of_capUB
    (p := LN2c * 2 ^ 27 * phaseErrorDen - phaseErrorNum * 2 ^ 99)
    (q := QS * phaseErrorDen) (y := 2) (w := 1)
    (by unfold phaseErrorDen QS; decide) (by decide) ln2WordMinusPhaseCap
  have harg :
      ((LN2c * 2 ^ 27 * phaseErrorDen - phaseErrorNum * 2 ^ 99 : Nat) : Real) /
          ((QS * phaseErrorDen : Nat) : Real) ≤ Real.log 2 := by
    apply (Real.le_log_iff_exp_le (by norm_num : (0 : Real) < 2)).2
    simpa using hexp
  have heq :
      ((LN2c * 2 ^ 27 * phaseErrorDen - phaseErrorNum * 2 ^ 99 : Nat) : Real) /
          ((QS * phaseErrorDen : Nat) : Real) =
        ln2Word - (phaseErrorNum : Real) / (10 ^ 27 * phaseErrorDen) := by
    norm_num [ln2Word, LN2c, QS, phaseErrorNum, phaseErrorDen]
  rw [heq] at harg
  unfold phaseDeltaRay
  have hden : (0 : Real) < (phaseErrorDen : Real) := by
    norm_num [phaseErrorDen]
  have hscale : (0 : Real) < 10 ^ 27 := by positivity
  have hsmall : ln2Word - Real.log 2 ≤
      (phaseErrorNum : Real) / (10 ^ 27 * phaseErrorDen) := by
    linarith
  calc
    10 ^ 27 * (ln2Word - Real.log 2) ≤
        10 ^ 27 * ((phaseErrorNum : Real) / (10 ^ 27 * phaseErrorDen)) :=
      mul_le_mul_of_nonneg_left hsmall hscale.le
    _ = (phaseErrorNum : Real) / phaseErrorDen := by
      field_simp [hden.ne', hscale.ne']; ring

theorem phaseErrorRay_le {k : Int} (hlo : -95 ≤ k) (hhi : k ≤ 159) :
    phaseErrorRay k ≤ (159 : Real) * phaseErrorNum / phaseErrorDen := by
  by_cases hk : k ≤ 0
  · have hkR : (k : Real) ≤ 0 := by exact_mod_cast hk
    have herr : phaseErrorRay k ≤ 0 := by
      unfold phaseErrorRay
      exact mul_nonpos_of_nonpos_of_nonneg hkR phaseDeltaRay_nonneg
    exact herr.trans (by positivity)
  · have hkR : (k : Real) ≤ 159 := by exact_mod_cast hhi
    have hk0R : (0 : Real) ≤ k := by exact_mod_cast (show 0 ≤ k by omega)
    unfold phaseErrorRay
    calc
      (k : Real) * phaseDeltaRay
          ≤ (k : Real) * ((phaseErrorNum : Real) / phaseErrorDen) :=
        mul_le_mul_of_nonneg_left phaseDeltaRay_le hk0R
      _ ≤ (159 : Real) * ((phaseErrorNum : Real) / phaseErrorDen) :=
        mul_le_mul_of_nonneg_right hkR (by positivity)
      _ = (159 : Real) * phaseErrorNum / phaseErrorDen := by ring

theorem core_add_phase_lt_global {e : Real} {k : Int}
    (he : e < (coreErrorNum : Real) / coreErrorDen)
    (hlo : -95 ≤ k) (hhi : k ≤ 159) :
    e + phaseErrorRay k < (globalErrorNum : Real) / globalErrorDen := by
  calc
    e + phaseErrorRay k <
        (coreErrorNum : Real) / coreErrorDen +
          (159 : Real) * phaseErrorNum / phaseErrorDen :=
      add_lt_add_of_lt_of_le he (phaseErrorRay_le hlo hhi)
    _ < (globalErrorNum : Real) / globalErrorDen := by
      norm_num [coreErrorNum, coreErrorDen, phaseErrorNum, phaseErrorDen,
        globalErrorNum, globalErrorDen]

theorem biasPlusGlobalErrorCap :
    capUB
      (BIASc * 2 ^ 27 * globalErrorDen + globalErrorNum * 2 ^ 99)
      (QS * globalErrorDen) Sc (10 ^ 18) := by
  refine capUB_of_partial (K := 130)
    (by unfold globalErrorDen QS; decide) (by decide) ?_
  decide

theorem biasPlusGlobalErrorExpLe :
    Real.exp (biasNatural +
        ((globalErrorNum : Real) / globalErrorDen) / 10 ^ 27) ≤
      (Sc : Real) / 10 ^ 18 := by
  have hexp := exp_le_of_capUB
    (p := BIASc * 2 ^ 27 * globalErrorDen + globalErrorNum * 2 ^ 99)
    (q := QS * globalErrorDen) (y := Sc) (w := 10 ^ 18)
    (by unfold globalErrorDen QS; decide) (by decide) biasPlusGlobalErrorCap
  have heq :
      (((BIASc * 2 ^ 27 * globalErrorDen + globalErrorNum * 2 ^ 99 : Nat) : Real) /
          ((QS * globalErrorDen : Nat) : Real)) =
        biasNatural + ((globalErrorNum : Real) / globalErrorDen) / 10 ^ 27 := by
    norm_num [biasNatural, BIASc, globalErrorNum, globalErrorDen, QS]
  rw [← heq]
  norm_num at hexp ⊢
  exact hexp

theorem bias_add_core_phase_exp_lt {e : Real} {k : Int}
    (he : e < (coreErrorNum : Real) / coreErrorDen)
    (hlo : -95 ≤ k) (hhi : k ≤ 159) :
    Real.exp (biasNatural + (e + phaseErrorRay k) / 10 ^ 27) <
      (Sc : Real) / 10 ^ 18 := by
  have herr := core_add_phase_lt_global he hlo hhi
  have harg : biasNatural + (e + phaseErrorRay k) / 10 ^ 27 <
      biasNatural + ((globalErrorNum : Real) / globalErrorDen) / 10 ^ 27 := by
    exact add_lt_add_left (div_lt_div_of_pos_right herr (by positivity)) _
  exact (Real.exp_lt_exp.mpr harg).trans_le biasPlusGlobalErrorExpLe

end

end LnFloorCarry

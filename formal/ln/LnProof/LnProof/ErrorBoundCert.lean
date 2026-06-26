import LnProof.FloorAssembly

/-! Certificate constants for the `lnWadToRay` 1.698600000 ulp upper error
bound; the theorems below are checked by Lean's kernel. -/

namespace LnFloorCert

open LnExp LnFloor LnYul

def lnErrorBoundNum : Nat := 1698600000
def lnErrorBoundDen : Nat := 1000000000
def lnErrorExtraNum : Nat := lnErrorBoundNum - lnErrorBoundDen
def lnErrorExtraCap : Nat := 6986
def lnErrorBiasCap : Nat := 3384
def lnErrorCoarseGePosBudgetCap : Nat := 6961
def lnErrorCoarsePosBudgetCap : Nat := 6986
def lnErrorCoarseNegBudgetCap : Nat := 6785
def lnErrorCoarseGePosResidue : Nat := 0
def lnErrorCoarsePosResidue : Nat := 0
def lnErrorDirectResidueGap : Nat := 336460000000000000

/-- `e^((0.698600000)·10^-27) ≥ 1 + 6986·10^-31`. -/
theorem capEFracL :
    capLB (lnErrorExtraNum * 2 ^ 99) (QS * lnErrorBoundDen)
      (10 ^ 31 + lnErrorExtraCap) (10 ^ 31) :=
  ⟨1, by decide +kernel⟩

/-- The positive-shift coarse budget needs this much checked phase residue
in addition to the published fractional ulp. -/
theorem capECoarsePosL :
    capLB (lnErrorExtraNum * 2 ^ 99 + lnErrorCoarsePosResidue) (QS * lnErrorBoundDen)
      (10 ^ 31 + lnErrorCoarsePosBudgetCap) (10 ^ 31) :=
  ⟨1, by decide +kernel⟩

/-- The ge positive-shift branch has the stronger mantissa lower bound
`m >= Sc`, so it needs less checked phase residue than the full positive
branch. -/
theorem capECoarseGePosL :
    capLB (lnErrorExtraNum * 2 ^ 99 + lnErrorCoarseGePosResidue) (QS * lnErrorBoundDen)
      (10 ^ 31 + lnErrorCoarseGePosBudgetCap) (10 ^ 31) :=
  ⟨1, by decide +kernel⟩

/-- Negative-shift budgets use a weaker coarse cap, directly implied by the
same fractional ulp witness. -/
theorem capECoarseNegL :
    capLB (lnErrorExtraNum * 2 ^ 99) (QS * lnErrorBoundDen)
      (10 ^ 31 + lnErrorCoarseNegBudgetCap) (10 ^ 31) :=
  ⟨1, by decide +kernel⟩

theorem capBiasL3403 :
    capLB (BIASc * 2 ^ 27) QS (Sc * (10 ^ 31 - lnErrorBiasCap))
      (10 ^ 18 * 10 ^ 31) :=
  ⟨130, by unfold lnErrorBiasCap; decide +kernel⟩

/-- Nonnegative-shift strict lower budget with the fractional extra ulp. -/
def errBudgetL (k : Nat) : Bool :=
  decide (((Sc - 45) + 1) * 2 ^ k * (10 ^ 40 : Nat) ^ k * 10 ^ 142 ≤
    (Sc - 45) * (10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ k * (10 ^ 31 - 3384) *
      (10 ^ 31 + lnErrorCoarsePosBudgetCap) * (10 ^ 31 - 10) * 10 ^ 18)

/-- Ge positive-shift strict lower budget. This uses `m >= Sc` rather than
the full positive-shift `m >= 2^95` lower bound. -/
def errBudgetLGe (k : Nat) : Bool :=
  decide ((Sc + 1) * 2 ^ k * (10 ^ 40 : Nat) ^ k * 10 ^ 142 ≤
    Sc * (10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ k * (10 ^ 31 - 3384) *
      (10 ^ 31 + lnErrorCoarseGePosBudgetCap) * (10 ^ 31 - 10) * 10 ^ 18)

/-- Negative-shift strict lower budget with the fractional extra ulp. -/
def errBudgetLn (j : Nat) : Bool :=
  decide ((10 : Nat) ^ 142 * (2 * (10 ^ 40 + 1)) ^ j ≤
    2 ^ j * (10 ^ 40 : Nat) ^ j * (10 ^ 31 - 3385) * (10 ^ 31 - 3384) *
      (10 ^ 31 + lnErrorCoarseNegBudgetCap) * (10 ^ 31 - 10) * 10 ^ 18)

/-- Reciprocal nonnegative-shift strict budget with the fractional extra ulp. -/
def errBudgetB (k : Nat) : Bool :=
  decide ((10 : Nat) ^ 31 * (10 ^ 40 : Nat) ^ k * (10 ^ 18 * 10 ^ 31) * 10 ^ 31 *
      (((Sc - 45) + 1) * 2 ^ k) * 10 ^ 31 ≤
    10 ^ 18 * (10 ^ 31 - 10) * (Sc - 45) * (10 ^ 31 - 3385) *
      (2 * (10 ^ 40 - 1)) ^ k * (10 ^ 31 - 3384) *
      (10 ^ 31 + lnErrorCoarsePosBudgetCap))

/-- Reciprocal negative-shift strict budget with the fractional extra ulp. -/
def errBudgetBn (j : Nat) : Bool :=
  decide ((2 * (10 ^ 40 + 1)) ^ j * (10 : Nat) ^ 31 * (10 ^ 18 * 10 ^ 31) *
      10 ^ 31 * 10 ^ 31 ≤
    10 ^ 18 * (10 ^ 31 - 10) * (10 ^ 40 : Nat) ^ j * 2 ^ j *
      (10 ^ 31 - 3385) * (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarseNegBudgetCap))

theorem errBudgetL_all : (List.range 160).all errBudgetL = true := by
  decide +kernel

theorem errBudgetLGe_all : (List.range 160).all errBudgetLGe = true := by
  decide +kernel

theorem errBudgetLn_all : (List.range 96).all errBudgetLn = true := by
  decide +kernel

theorem errBudgetB_all : (List.range 160).all errBudgetB = true := by
  decide +kernel

theorem errBudgetBn_all : (List.range 96).all errBudgetBn = true := by
  decide +kernel

theorem errBudgetL_le {k : Nat} (hk : k ≤ 159) :
    ((Sc - 45) + 1) * 2 ^ k * (10 ^ 40 : Nat) ^ k * 10 ^ 142 ≤
      (Sc - 45) * (10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ k * (10 ^ 31 - 3384) *
        (10 ^ 31 + lnErrorCoarsePosBudgetCap) * (10 ^ 31 - 10) * 10 ^ 18 := by
  have h := List.all_eq_true.mp errBudgetL_all k (List.mem_range.mpr (by omega))
  simp only [errBudgetL, decide_eq_true_eq] at h
  exact h

theorem errBudgetLGe_le {k : Nat} (hk : k ≤ 159) :
    (Sc + 1) * 2 ^ k * (10 ^ 40 : Nat) ^ k * 10 ^ 142 ≤
      Sc * (10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ k * (10 ^ 31 - 3384) *
        (10 ^ 31 + lnErrorCoarseGePosBudgetCap) * (10 ^ 31 - 10) * 10 ^ 18 := by
  have h := List.all_eq_true.mp errBudgetLGe_all k (List.mem_range.mpr (by omega))
  simp only [errBudgetLGe, decide_eq_true_eq] at h
  exact h

theorem errBudgetLn_le {j : Nat} (hj : j ≤ 95) :
    (10 : Nat) ^ 142 * (2 * (10 ^ 40 + 1)) ^ j ≤
      2 ^ j * (10 ^ 40 : Nat) ^ j * (10 ^ 31 - 3385) * (10 ^ 31 - 3384) *
        (10 ^ 31 + lnErrorCoarseNegBudgetCap) * (10 ^ 31 - 10) * 10 ^ 18 := by
  have h := List.all_eq_true.mp errBudgetLn_all j (List.mem_range.mpr (by omega))
  simp only [errBudgetLn, decide_eq_true_eq] at h
  exact h

theorem errBudgetB_le {k : Nat} (hk : k ≤ 159) :
    (10 : Nat) ^ 31 * (10 ^ 40 : Nat) ^ k * (10 ^ 18 * 10 ^ 31) * 10 ^ 31 *
      (((Sc - 45) + 1) * 2 ^ k) * 10 ^ 31 ≤
    10 ^ 18 * (10 ^ 31 - 10) * (Sc - 45) * (10 ^ 31 - 3385) *
      (2 * (10 ^ 40 - 1)) ^ k * (10 ^ 31 - 3384) *
      (10 ^ 31 + lnErrorCoarsePosBudgetCap) := by
  have h := List.all_eq_true.mp errBudgetB_all k (List.mem_range.mpr (by omega))
  simp only [errBudgetB, decide_eq_true_eq] at h
  exact h

theorem errBudgetBn_le {j : Nat} (hj : j ≤ 95) :
    (2 * (10 ^ 40 + 1)) ^ j * (10 : Nat) ^ 31 * (10 ^ 18 * 10 ^ 31) * 10 ^ 31 *
      10 ^ 31 ≤
    10 ^ 18 * (10 ^ 31 - 10) * (10 ^ 40 : Nat) ^ j * 2 ^ j *
      (10 ^ 31 - 3385) * (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarseNegBudgetCap) := by
  have h := List.all_eq_true.mp errBudgetBn_all j (List.mem_range.mpr (by omega))
  simp only [errBudgetBn, decide_eq_true_eq] at h
  exact h

/-- Nonnegative-shift strict lower budget at `k = 0` without discarded-bit
padding.  Here the mantissa window is exact (`x = m`), so the fractional
error cap is sufficient. -/
theorem errBudgetL0_exact :
    (10 : Nat) ^ 142 ≤
      (10 ^ 31 - 3385) * (10 ^ 31 - 3384) *
        (10 ^ 31 + lnErrorExtraCap) * (10 ^ 31 - 10) * 10 ^ 18 := by
  decide +kernel

end LnFloorCert

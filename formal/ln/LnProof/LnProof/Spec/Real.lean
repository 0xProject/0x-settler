import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic

/-!
# Public `lnWad` real specifications

The public correctness target is a fixed-point bracket around `Real.log`.
The EVM-side modules prove that generated runtime outputs satisfy these
predicates for signed positive int256 inputs.
-/

namespace LnRealSpec

noncomputable section

def WAD : Nat := 10 ^ 18
def RAY : Nat := 10 ^ 27

def wadRatio (x : Nat) : Real :=
  (x : Real) / WAD

def lnWadToRayTarget (x : Nat) : Real :=
  RAY * Real.log (wadRatio x)

def lnWadTarget (x : Nat) : Real :=
  WAD * Real.log (wadRatio x)

def LnWadToRaySpec (x : Nat) (r : Int) : Prop :=
  (r : Real) ≤ lnWadToRayTarget x ∧ lnWadToRayTarget x < ((r + 2 : Int) : Real)

def LnWadSpec (x : Nat) (w : Int) : Prop :=
  (w : Real) ≤ lnWadTarget x ∧ lnWadTarget x < ((w + 2 : Int) : Real)

theorem wadRatio_wad : wadRatio WAD = 1 := by
  unfold wadRatio WAD
  norm_num

theorem lnWadToRayTarget_wad : lnWadToRayTarget WAD = 0 := by
  simp [lnWadToRayTarget, wadRatio_wad]

theorem lnWadTarget_wad : lnWadTarget WAD = 0 := by
  simp [lnWadTarget, wadRatio_wad]

theorem lnWadToRaySpec_zero : LnWadToRaySpec WAD 0 := by
  unfold LnWadToRaySpec
  rw [lnWadToRayTarget_wad]
  norm_num

theorem lnWadSpec_zero : LnWadSpec WAD 0 := by
  unfold LnWadSpec
  rw [lnWadTarget_wad]
  norm_num

end

end LnRealSpec

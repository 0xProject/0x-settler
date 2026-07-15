import Common.Foundation.KroneckerShift

namespace Common.Poly

structure PackedShiftScalars where
  shiftedL1Bound : Nat
  sourceAevalBound : Nat
  evalAtRadix : Int

def literalPackedShiftScalars (B : Nat) (C S : List Int) (a : Int) :
    PackedShiftScalars where
  shiftedL1Bound := polyL1 S
  sourceAevalBound := aeval C (1 + a.natAbs)
  evalAtRadix := evalPoly S (((2 ^ B : Nat) : Int))

def checkPackedShiftScalars (B : Nat) (s : PackedShiftScalars) : Bool :=
  decide (s.shiftedL1Bound * 2 < 2 ^ B) &&
    decide (s.sourceAevalBound * 2 < 2 ^ B)

theorem checkPackedShiftScalars_sound {B : Nat} {s : PackedShiftScalars}
    (h : checkPackedShiftScalars B s = true) :
    s.shiftedL1Bound * 2 < 2 ^ B ∧ s.sourceAevalBound * 2 < 2 ^ B := by
  simpa only [checkPackedShiftScalars, Bool.and_eq_true, decide_eq_true_eq] using h

structure PackedShiftEvidence (B : Nat) (C S : List Int) (a : Int)
    (s : PackedShiftScalars) : Prop where
  shiftedL1_le : polyL1 S ≤ s.shiftedL1Bound
  sourceAeval_le : aeval C (1 + a.natAbs) ≤ s.sourceAevalBound
  shifted_eval : evalPoly S (((2 ^ B : Nat) : Int)) = s.evalAtRadix
  source_eval : evalPoly C (a + ((2 ^ B : Nat) : Int)) = s.evalAtRadix

theorem literalPackedShiftEvidence {B : Nat} {C S : List Int} {a : Int}
    (heval : evalPoly S (((2 ^ B : Nat) : Int)) =
      evalPoly C (a + ((2 ^ B : Nat) : Int))) :
    PackedShiftEvidence B C S a (literalPackedShiftScalars B C S a) where
  shiftedL1_le := Nat.le_refl _
  sourceAeval_le := Nat.le_refl _
  shifted_eval := rfl
  source_eval := heval.symm

theorem packedShift_eval {B : Nat} {C S : List Int} {a : Int}
    {s : PackedShiftScalars}
    (hcheck : checkPackedShiftScalars B s = true)
    (he : PackedShiftEvidence B C S a s) :
    ∀ x : Int, evalPoly S x = evalPoly C (a + x) := by
  obtain ⟨hshifted, hsource⟩ := checkPackedShiftScalars_sound hcheck
  have hS : polyL1 S * 2 < 2 ^ B := by
    have hbound := he.shiftedL1_le
    omega
  have htrueShift : polyL1 (polyShift C a) * 2 < 2 ^ B := by
    have hpolyShift := polyL1_polyShift C a
    have hbound := he.sourceAeval_le
    omega
  have hradix :
      evalPoly S ((2 : Int) ^ B) = evalPoly (polyShift C a) ((2 : Int) ^ B) := by
    rw [int_two_pow, polyShift_eval]
    exact he.shifted_eval.trans he.source_eval.symm
  intro x
  rw [evalPoly_ext S (polyShift C a) hS htrueShift hradix x]
  exact polyShift_eval C a x

def checkPackedCell (B : Nat) (S : List Int) (w : Int)
    (s : PackedShiftScalars) : Bool :=
  checkPackedShiftScalars B s && decide (0 ≤ w) &&
    decide (0 ≤ (hornerIv S 0 w).1)

theorem checkPackedCell_nonnegOn {B : Nat} {C S : List Int} {a w : Int}
    {s : PackedShiftScalars}
    (he : PackedShiftEvidence B C S a s)
    (hcheck : checkPackedCell B S w s = true) :
    NonnegOn C a (a + w) := by
  simp only [checkPackedCell, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨⟨hpacked, hw⟩, hhorner⟩ := hcheck
  have heval := packedShift_eval hpacked he
  intro x hxlo hxhi
  have hs := (hornerIv_sound S (lo := 0) (hi := w) (x := x - a)
    (Int.le_refl 0) (by omega) (by omega)).1
  rw [heval (x - a)] at hs
  rw [show a + (x - a) = x by omega] at hs
  omega

end Common.Poly

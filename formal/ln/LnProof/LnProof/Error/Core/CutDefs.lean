import LnProof.Floor.CutEquiv
import LnProof.Error.Cert

/-!
# Error bound — CutDefs

Cut predicates, scale constants, and the strict-to-exact bridge.
-/

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

namespace LnFloorCert

open LnYul LnFloor Common.Exp Common.Poly

attribute [local irreducible] lnWadToRayBody


theorem capLB_lift_right {p q y w den : Nat} (hq : 0 < q)
    (h : capLB p q y w) : capLB (p * den) (q * den) y w := by
  refine capLB_arg (q' := q) hq ?_ h
  rw [← Nat.mul_assoc, Nat.mul_right_comm p den q]

theorem capUB_lift_right {p q y w den : Nat} (hq : 0 < q)
    (h : capUB p q y w) : capUB (p * den) (q * den) y w := by
  refine capUB_arg (q' := q) hq ?_ h
  rw [Nat.mul_right_comm p den q]
  rw [Nat.mul_assoc]

/-- Internal strict-margin version inherited from the floor proof.  Its
`10^31 - 10` denominator is much stronger than the exact rational cut below
and is reused only where the existing branch proofs already establish it. -/
def CutLogWadRayLtRationalStrict (x : Nat) (r : Int) (num den : Nat) : Prop :=
  if 1 ≤ r * (den : Int) + (num : Int) then
    CutRatioLeExp (x * 10 ^ 31) (10 ^ 18 * (10 ^ 31 - 10))
      ((r * (den : Int) + (num : Int)).toNat * 2 ^ 99) (QS * den)
  else
    CutExpLe ((-(r * (den : Int) + (num : Int))).toNat * 2 ^ 99) (QS * den)
      (10 ^ 18 * (10 ^ 31 - 10)) (x * 10 ^ 31)

/-- Rational upper-cut predicate for wad-input, ray-output logarithms.

`CutLogWadRayLtRational x r num den` is the real-free counterpart of
`10^27 * log(x / 10^18) < r + num / den`.  The positive-exponent branch proves
a lower exponential cut for `(r * den + num) / den`; the reciprocal branch
proves the corresponding upper exponential cut for the negated exponent. -/
def CutLogWadRayLtRational (x : Nat) (r : Int) (num den : Nat) : Prop :=
  if 1 ≤ r * (den : Int) + (num : Int) then
    CutRatioLeExp x (10 ^ 18)
      ((r * (den : Int) + (num : Int)).toNat * 2 ^ 99) (QS * den)
  else
    CutExpLe ((-(r * (den : Int) + (num : Int))).toNat * 2 ^ 99) (QS * den)
      (10 ^ 18) x

def lnErrQ : Nat := QS * lnErrorBoundDen
def lnErrArg (r : Int) : Nat :=
  (r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)).toNat * 2 ^ 99
def lnErrNegArg (r : Int) : Nat :=
  (-(r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int))).toNat * 2 ^ 99
def wadRayNum (x : Nat) : Nat := x * 10 ^ 31
def wadRayStrictDen : Nat := 10 ^ 18 * (10 ^ 31 - 10)
def posTopX (c m : Nat) : Nat := (m + 1) * 2 ^ (160 - c) - 1
def twoPow27N : Nat := 2 ^ 27
def twoPow99N : Nat := 2 ^ 99
def twoPow27I : Int := 2 ^ 27
def twoPow72I : Int := 2 ^ 72
def twoPow99I : Int := 2 ^ 99
def lnPhaseScaleN : Nat := 1000000000000000000000000000
def lnPhaseScaleI : Int := 1000000000000000000000000000
def lnBiasI : Int := 116873961749927929127912020551560854268589826112230

/-- First-order exact-wad budget with the common `10^18` and `2^99` factors
cancelled out. -/
theorem wad_exact_upper_budget :
    10 ^ 31 * (10 ^ 27 * lnErrorBoundDen) ≤
      (10 ^ 27 * lnErrorBoundDen + lnErrorBoundNum) * (10 ^ 31 - 10) := by
  unfold lnErrorBoundDen lnErrorBoundNum
  decide +kernel

theorem capLB_strict_to_exact {p q x : Nat}
    (h : capLB p q (wadRayNum x) wadRayStrictDen) : capLB p q x (10 ^ 18) := by
  refine capLB_weaken (p := p) (q := q) (y := wadRayNum x) (w := wadRayStrictDen)
    (y' := x) (w' := 10 ^ 18) (by unfold wadRayStrictDen; decide) h ?_
  unfold wadRayNum wadRayStrictDen
  have hden : 10 ^ 18 * (10 ^ 31 - 10) ≤ 10 ^ 18 * 10 ^ 31 := by
    exact Nat.mul_le_mul_left _ (by decide : (10 ^ 31 - 10 : Nat) ≤ 10 ^ 31)
  calc
    x * (10 ^ 18 * (10 ^ 31 - 10)) ≤ x * (10 ^ 18 * 10 ^ 31) :=
      Nat.mul_le_mul_left _ hden
    _ = x * 10 ^ 31 * 10 ^ 18 := by
      simp only [Nat.mul_comm, Nat.mul_left_comm]

theorem capUB_strict_to_exact {p q x : Nat} (hx : 0 < x)
    (h : capUB p q wadRayStrictDen (wadRayNum x)) : capUB p q (10 ^ 18) x := by
  refine capUB_weaken (p := p) (q := q) (y := wadRayStrictDen) (w := wadRayNum x)
    (y' := 10 ^ 18) (w' := x) ?_ h ?_
  · unfold wadRayNum
    exact Nat.mul_pos hx (by decide)
  · unfold wadRayNum wadRayStrictDen
    have hden : 10 ^ 31 - 10 ≤ (10 ^ 31 : Nat) := by decide
    calc
      (10 ^ 18 * (10 ^ 31 - 10)) * x ≤ (10 ^ 18 * 10 ^ 31) * x :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hden)
      _ = 10 ^ 18 * (x * 10 ^ 31) := by
        simp only [Nat.mul_comm, Nat.mul_left_comm]

theorem CutLogWadRayLtRational_of_strict {x : Nat} {r : Int} {num den : Nat}
    (hx : 0 < x) :
    CutLogWadRayLtRationalStrict x r num den →
      CutLogWadRayLtRational x r num den := by
  intro h
  unfold CutLogWadRayLtRationalStrict at h
  unfold CutLogWadRayLtRational
  by_cases hpos : 1 ≤ r * (den : Int) + (num : Int)
  · rw [if_pos hpos] at h ⊢
    exact capLB_strict_to_exact h
  · rw [if_neg hpos] at h ⊢
    exact capUB_strict_to_exact hx h

end LnFloorCert

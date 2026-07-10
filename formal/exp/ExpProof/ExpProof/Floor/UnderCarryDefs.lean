import ExpProof.Floor.CertDefsV
import ExpProof.Floor.GranPieces

/-!
# Positive-under carry certificates at the signed 128-bit magnitude bound

The carry budget is reduced to one degree-ten integer polynomial on each
granularity interval.  Every row records the interval, its argument cap, and
the checked integer bound used by the corresponding certificate.
-/

namespace ExpCertV

open Common.Poly

def S2 : Int := 2 ^ 127 - 1

def denAtCap (T : Int) : List Int :=
  polySub (polyScale (2 ^ 111) evVPoly) (polyScale T odVPoly)

def carryLhs (T : Int) : List Int :=
  let D := denAtCap T
  let inner := polyAdd
    (polyAdd (polyScale (200 * S2) D) (polyScale (200 * S2 * T) odVPoly))
    (polyScale (800 * S2 * 2 ^ 637) [1])
  polyAdd
    (polyScale (1000 * (2 ^ 637 + 269746241 * 2 ^ 480 * T)) inner)
    (polyScale (200000 * 2 ^ 637) D)

def carryCert (T R : Int) : List Int :=
  let D := denAtCap T
  polySub (polyScale R (polyMul D D)) (carryLhs T)

def underCarryBounds : List Int := [
  92600, 97310, 101060, 104316, 107259, 109980, 112535, 114960,
  117278, 119508, 121663, 123754, 125790, 127776, 129719, 131623,
  133492, 135329, 137138, 138920, 140678, 142414, 144130, 145826,
  147505, 149168, 150816, 152449, 154069, 155677, 157272, 158857]

def withCarryBound :
    (Int × Int × Int × Int × Int) → Int → (Int × Int × Int × Int)
  | (vlo, vhi, T, _, _), R => (vlo, vhi, T, R)

def underCarryPieces : List (Int × Int × Int × Int) :=
  List.zipWith withCarryBound granPieces underCarryBounds

theorem eval_denAtCap (T v : Int) :
    evalPoly (denAtCap T) v =
      2 ^ 111 * evalPoly evVPoly v - T * evalPoly odVPoly v := by
  simp only [denAtCap, evalPoly_polySub, evalPoly_polyScale]

theorem eval_carryLhs (T v : Int) :
    evalPoly (carryLhs T) v =
      1000 * (2 ^ 637 + 269746241 * 2 ^ 480 * T) *
        (200 * S2 * evalPoly (denAtCap T) v +
          200 * S2 * T * evalPoly odVPoly v + 800 * S2 * 2 ^ 637) +
      200000 * 2 ^ 637 * evalPoly (denAtCap T) v := by
  simp only [carryLhs, evalPoly_polyAdd, evalPoly_polyScale, evalPoly_singleton]
  rw [Int.mul_one]

theorem eval_carryCert (T R v : Int) :
    evalPoly (carryCert T R) v =
      R * (evalPoly (denAtCap T) v * evalPoly (denAtCap T) v) -
        evalPoly (carryLhs T) v := by
  simp only [carryCert, evalPoly_polySub, evalPoly_polyScale, evalPoly_polyMul]

end ExpCertV

import LnProof.Model.Body

namespace LnFloorCarry

open Common.Poly LnYul

def approximationScale : Nat := 2 ^ 96
def approximationMaxU : Nat := Uc
def approximationTerms : Nat := 42

def approximationOddProduct : Int :=
  (List.range approximationTerms).foldl
    (fun a (j : Nat) => a * (2 * (j : Int) + 1)) 1

def approximationTaylorDen : Int :=
  85 * approximationOddProduct *
    (approximationScale : Int) ^ (approximationTerms - 1)

def approximationTaylorNum : List Int :=
  (List.range approximationTerms).map fun (j : Nat) =>
    85 * (approximationOddProduct / (2 * (j : Int) + 1)) *
      (approximationScale : Int) ^ (approximationTerms - 1 - j)

def approximationTailPower : List Int :=
  List.replicate approximationTerms 0 ++ [1]

def approximationOneMinus : List Int := [(approximationScale : Int), -1]
def approximationRationalDen : List Int := polyNeg QQc
def approximationRationalNum : List Int := polyScale (2 ^ 28) PPc

def approximationUpperNum : List Int :=
  polyAdd
    (polyMul approximationTaylorNum approximationOneMinus)
    (polyScale approximationOddProduct approximationTailPower)

def approximationUpperDen : List Int :=
  polyScale approximationTaylorDen approximationOneMinus

def approximationLowGapNum : List Int :=
  polyAdd
    (polyMul approximationUpperNum approximationRationalDen)
    (polyScale (-1)
      (polyMul approximationRationalNum approximationUpperDen))

def approximationLowGapDen : List Int :=
  polyMul approximationUpperDen approximationRationalDen

def approximationHighGapNum : List Int :=
  polyAdd
    (polyScale approximationTaylorDen approximationRationalNum)
    (polyScale (-1)
      (polyMul approximationTaylorNum approximationRationalDen))

def approximationHighGapDen : List Int :=
  polyScale approximationTaylorDen approximationRationalDen

def approximationErrorNum : Nat := 323661607720025115242513
def approximationErrorDen : Nat := 10 ^ 24
def approximationEnvelopeDen : Nat := 10 ^ 60

def approximationEnvelopeSquareBudget : Nat :=
  approximationErrorNum ^ 2 * 10 ^ 18 * 2 ^ 94

def approximationEnvelopeCandidate (hi a : Nat) : Prop :=
  a ^ 2 * (hi + 1) ≤ approximationEnvelopeSquareBudget

def approximationLowCert (a : Nat) : List Int :=
  polyAdd
    (polyScale a approximationLowGapDen)
    (polyScale (-(approximationEnvelopeDen : Int)) approximationLowGapNum)

def approximationHighCert (a : Nat) : List Int :=
  polyAdd
    (polyScale a approximationHighGapDen)
    (polyScale (-(approximationEnvelopeDen : Int)) approximationHighGapNum)

end LnFloorCarry

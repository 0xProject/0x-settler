import LnProof.ShiftCert
import LnProof.Stages

/-!
# Floor-specification bracket polynomials

The bracket rationals for `X1/2^99` as integer polynomials in the
mantissa, homogenized directly over the `Stages` coefficient lists
`PPc`/`QQc` (denominators `8 B²` at the `wlo` points, `B²` at `w*`), with
the stage truncation slops entering exactly as `SLOPPc (B²)^4` and
`SLOPQc (8 B²)^5`. The `checkCover` certificates over these polynomials
are in the `FloorCert*` files.
-/

namespace LnFloorCert

open LnPoly LnYul

def WINDOW : Nat := 46

def geA : List Int := [-(Sc : Int), 1]
def geB : List Int := [(Sc : Int), 1]
def geA2 : List Int := polyMul geA geA
def geB2 : List Int := polyMul geB geB
def geWLO : List Int := polyAdd (polyAdd (polyScale (2 ^ 99) geA2) (polyNeg (polyMul geA geB))) (polyScale (-8) geB2)
def geD8 : List Int := polyScale 8 geB2
def geA96 : List Int := polyScale (2 ^ 96) geA2
def gePPHwlo : List Int := homPoly PPc geWLO geD8
def gePPHws : List Int := homPoly PPc geA96 geB2
def geQQHws : List Int := homPoly QQc geA96 geB2
def geQQHwlo : List Int := homPoly QQc geWLO geD8
def geTN : List Int := polyScale (2 ^ 17) (polyMul (polyMul geA geB) gePPHwlo)
def geTD : List Int := polyNeg geQQHws
def gePLOP : List Int := polyAdd gePPHws (polyScale (-SLOPPc) (polyPow geB2 4))
def geDLO : List Int := polyAdd (polyNeg geQQHwlo) (polyScale SLOPQc (polyPow geD8 5))
def geAZ : List Int := polyAdd (polyScale (2 ^ 100) geA) (polyNeg geB)
def geTN2 : List Int := polyMul (polyMul gePLOP geAZ) geB
def geTD2 : List Int := polyScale (2 ^ 56) geDLO
def geTN2b : List Int := polyAdd (polyScale (2 ^ 99) geTN2) (polyNeg geTD2)
def geTD2b : List Int := polyScale (2 ^ 99) geTD2

def ltA : List Int := [(Sc : Int), -1]
def ltB : List Int := [(Sc : Int), 1]
def ltA2 : List Int := polyMul ltA ltA
def ltB2 : List Int := polyMul ltB ltB
def ltWLO : List Int := polyAdd (polyAdd (polyScale (2 ^ 99) ltA2) (polyNeg (polyMul ltA ltB))) (polyScale (-8) ltB2)
def ltD8 : List Int := polyScale 8 ltB2
def ltA96 : List Int := polyScale (2 ^ 96) ltA2
def ltPPHwlo : List Int := homPoly PPc ltWLO ltD8
def ltPPHws : List Int := homPoly PPc ltA96 ltB2
def ltQQHws : List Int := homPoly QQc ltA96 ltB2
def ltQQHwlo : List Int := homPoly QQc ltWLO ltD8
def ltTN : List Int := polyScale (2 ^ 17) (polyMul (polyMul ltA ltB) ltPPHwlo)
def ltTD : List Int := polyNeg ltQQHws
def ltPLOP : List Int := polyAdd ltPPHws (polyScale (-SLOPPc) (polyPow ltB2 4))
def ltDLO : List Int := polyAdd (polyNeg ltQQHwlo) (polyScale SLOPQc (polyPow ltD8 5))
def ltAZ : List Int := polyAdd (polyScale (2 ^ 100) ltA) (polyNeg ltB)
def ltTN2 : List Int := polyMul (polyMul ltPLOP ltAZ) ltB
def ltTD2 : List Int := polyScale (2 ^ 56) ltDLO
def ltTN2b : List Int := polyAdd (polyScale (2 ^ 99) ltTN2) (polyNeg ltTD2)
def ltTD2b : List Int := polyScale (2 ^ 99) ltTD2

def KF : Int := 1124000727777607680000
def KF1 : Int := 25852016738884976640000
/-- Never-overshoot margin floor (the +form certs `certGeUp`, `certLtUp`): the
bias keeps at least this much of its `1e-31`-unit margin.  Lowered to `3382`
when the bias is raised. -/
def EUN : Int := 3382
/-- Not-too-low margin ceiling (the −form certs `certGeLo`, `certLtLo`): an upper
bound on the bias margin.  Unchanged by raising the bias. -/
def EUNl : Int := 3385
def EUD : Int := 10 ^ 31

def certGeUp : List Int :=
  polyAdd (polyScale ((EUD + EUN) * KF1) (polyMul [0, 1] (polyPow geTD 23)))
    (polyScale (-(Sc : Int) * EUD) (polyAdd (polyScale 23 (polyMul (expPolyNum geTN geTD 22) geTD)) (polyScale 2 (polyPow geTN 23))))
def certGeLo : List Int :=
  polyAdd (polyScale (EUD * (Sc : Int)) (expPolyNum geTN2b geTD2b 22))
    (polyScale (-(EUD - EUNl) * KF) (polyMul [0, 1] (polyPow geTD2b 22)))
def certLtUp : List Int :=
  polyAdd (polyScale (EUD + EUN) (polyMul [0, 1] (expPolyNum ltTN2b ltTD2b 22)))
    (polyScale (-EUD * (Sc : Int) * KF) (polyPow ltTD2b 22))
def certLtLo : List Int :=
  polyAdd (polyScale ((Sc : Int) * EUD * KF1) (polyPow ltTD 23))
    (polyScale (-(EUD - EUNl)) (polyMul [0, 1] (polyAdd (polyScale 23 (polyMul (expPolyNum ltTN ltTD 22) ltTD)) (polyScale 2 (polyPow ltTN 23)))))
def UB : Int := 2333000000000000000000000000
def certGeWS : List Int := polyAdd (polyScale UB geB2) (polyScale (-(2 ^ 96)) geA2)
def certLtWS : List Int := polyAdd (polyScale UB ltB2) (polyScale (-(2 ^ 96)) ltA2)
def certGeH : List Int := polyAdd (polyScale 24 geTD) (polyScale (-2) geTN)
def certLtH : List Int := polyAdd (polyScale 24 ltTD) (polyScale (-2) ltTN)
def certGeTD : List Int := polyAdd geTD [-1]
def certGeTD2 : List Int := polyAdd geTD2b [-1]
def certLtTD : List Int := polyAdd ltTD [-1]
def certLtTD2 : List Int := polyAdd ltTD2b [-1]

end LnFloorCert

import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Rat.BigOperators
import LnProof.Floor.CarryIndependent.Arithmetic

open scoped BigOperators
open FormalYul FormalYul.Preservation

namespace LnFloorCarry

open Finset LnYul Common.Poly

noncomputable section

def wordQ100 : Nat := 1267650600228229401496703205376
def wordQ96 : Nat := 79228162514264337593543950336
def rayScale : Nat := 1000000000000000000000000000

def pScale : Nat :=
  587135645693458306972370149197334256843920637227079967676822742883052256278652110865924749596192175757983744

def qScale : Nat :=
  157608024785577916849116160400574455220318957081861786671793173616982887085988842445657065019539662563226511961227264

def endpointZWord : Nat := 217494458298375249691265569565
def endpointUWord : Nat := 2332259347626381040680638252

def normalizedZ (m : Nat) : Real := (int256 (zWord m) : Real) / wordQ100
def normalizedU (m : Nat) : Real := (uWord (zWord m) : Real) / wordQ96
def highNormalizedZ (m : Nat) : Real := (-int256 (zWord m) : Int) / wordQ100

def endpointZ : Real := (endpointZWord : Real) / wordQ100
def endpointT : Real := ((Sc : Real) - 2 ^ 95) / ((Sc : Real) + 2 ^ 95)
def endpointV : Real := endpointZ ^ 2

def exactP (u : Nat) : Real := (evalPoly PPc (u : Int) : Real) / pScale
def exactD (u : Nat) : Real := (-evalPoly QQc (u : Int) : Int) / qScale

def pError (u : Nat) : Real :=
  1 + (u : Real) / 2 ^ 87 *
    (1 + (u : Real) / 2 ^ 97 * (1 + (u : Real) / 2 ^ 90))

def dError (u : Nat) : Real :=
  1 + (u : Real) / 2 ^ 95 *
    (1 + (u : Real) / 2 ^ 88 * (1 + (u : Real) / 2 ^ 90))

def exactRatio (u : Nat) : Real := exactP u / exactD u

def shadowRatio (u : Nat) : Real :=
  (exactP u - pError u) / (exactD u + dError u)

def atanhSeries (v : Real) : Real :=
  ∑' j : Nat, v ^ j / (2 * j + 1)

def endpointDerivative : Real :=
  (∑ j ∈ range 48,
      (j + 1) * endpointV ^ j / (2 * (j + 1) + 1)) +
    endpointV ^ 48 / (2 * (1 - endpointV))

def approximationBudget : Real :=
  (323661607720025115242513 : Real) / 10 ^ 24

def zFloorBudget : Real :=
  (2 * rayScale / wordQ100) / (1 - endpointT ^ 2)

def uFloorBudget : Real :=
  2 * rayScale * endpointZ * endpointDerivative / wordQ96

def hornerBudget : Real :=
  let P := exactP endpointUWord
  let D := exactD endpointUWord
  let ep := pError endpointUWord
  let ed := dError endpointUWord
  2 * rayScale * endpointZ *
    (P * ed + ep * D) / (D * (D + ed))

def closingDivisionBudget : Real := 2 * rayScale / wordQ100

def coreErrorLimit : Real :=
  (32886404036042980977667 : Real) / 10 ^ 23

def lowShadow (m : Nat) : Real :=
  -2 * normalizedZ m * shadowRatio (uWord (zWord m)) + 2 / wordQ100

def highShadow (m : Nat) : Real :=
  2 * highNormalizedZ m * exactRatio (uWord (zWord m))

def approximationTerm (m : Nat) : Real :=
  2 * rayScale * normalizedZ m *
    (atanhSeries (normalizedU m) - exactRatio (uWord (zWord m)))

def hornerTerm (m : Nat) : Real :=
  2 * rayScale * normalizedZ m *
    (exactRatio (uWord (zWord m)) - shadowRatio (uWord (zWord m)))

def highApproximationTerm (m : Nat) : Real :=
  2 * rayScale * highNormalizedZ m *
    (exactRatio (uWord (zWord m)) - atanhSeries (normalizedU m))

theorem approximationBudget_lt_coreErrorLimit :
    approximationBudget < coreErrorLimit := by
  norm_num [approximationBudget, coreErrorLimit]

private theorem approximationBudget_eq_cast :
    approximationBudget = (Arithmetic.approximationBudget : Real) := by
  norm_num [approximationBudget, Arithmetic.approximationBudget]

private theorem zFloorBudget_eq_cast :
    zFloorBudget = (Arithmetic.zBound : Real) := by
  norm_num [zFloorBudget, Arithmetic.zBound, endpointT, Arithmetic.m0,
    Arithmetic.q100, Arithmetic.ray, rayScale, wordQ100, Sc]

private theorem uFloorBudget_eq_cast :
    uFloorBudget = (Arithmetic.uBound : Real) := by
  simp only [uFloorBudget, Arithmetic.uBound, endpointDerivative,
    Arithmetic.fpUpper, endpointV, Arithmetic.vz, endpointZ, Arithmetic.a,
    endpointZWord, Arithmetic.z0, Arithmetic.q100, Arithmetic.ray, rayScale,
    wordQ100, wordQ96]
  push_cast
  norm_num

private theorem hornerBudget_eq_cast :
    hornerBudget = (Arithmetic.hornerBound : Real) := by
  norm_num [hornerBudget, Arithmetic.hornerBound, exactP, Arithmetic.p,
    exactD, Arithmetic.d, pError, Arithmetic.pError, dError,
    Arithmetic.dError, endpointUWord, Arithmetic.u0, pScale, qScale,
    Arithmetic.a, endpointZ, endpointZWord, Arithmetic.z0, wordQ100,
    Arithmetic.q100, rayScale, Arithmetic.ray, PPc, QQc,
    Common.Poly.evalPoly]

private theorem closingDivisionBudget_eq_cast :
    closingDivisionBudget = (Arithmetic.closingDivisionBound : Real) := by
  norm_num [closingDivisionBudget, Arithmetic.closingDivisionBound,
    rayScale, Arithmetic.ray, wordQ100, Arithmetic.q100]

private theorem coreErrorLimit_eq_cast :
    coreErrorLimit =
      ((Arithmetic.coreNum / Arithmetic.coreDen : ℚ) : Real) := by
  norm_num [coreErrorLimit, Arithmetic.coreNum, Arithmetic.coreDen]

theorem totalBudget_lt_coreErrorLimit :
    approximationBudget + zFloorBudget + uFloorBudget + hornerBudget +
        closingDivisionBudget < coreErrorLimit := by
  rw [approximationBudget_eq_cast, zFloorBudget_eq_cast, uFloorBudget_eq_cast,
    hornerBudget_eq_cast, closingDivisionBudget_eq_cast, coreErrorLimit_eq_cast]
  norm_cast
  simpa only [Arithmetic.total] using Arithmetic.total_lt_core

end

end LnFloorCarry

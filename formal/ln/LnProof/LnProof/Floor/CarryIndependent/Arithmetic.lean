import Mathlib.Algebra.BigOperators.Field
import LnProof.Model.Body

open scoped BigOperators
open LnYul Common.Poly

namespace LnFloorCarry.Arithmetic

def m0 : Nat := 2 ^ 95
def q100 : Nat := 2 ^ 100
def ray : Nat := 10 ^ 27
def z0 : Nat := 217494458298375249691265569565
def u0 : Nat := 2332259347626381040680638252

def a : ℚ := z0 / q100
def vz : ℚ := a ^ 2
def p : ℚ := evalPoly PPc u0 / 2 ^ 358
def d : ℚ := -evalPoly QQc u0 / 2 ^ 386
def pError (u : ℚ) : ℚ :=
  1 + u / 2 ^ 87 * (1 + u / 2 ^ 97 * (1 + u / 2 ^ 90))
def dError (u : ℚ) : ℚ :=
  1 + u / 2 ^ 95 * (1 + u / 2 ^ 88 * (1 + u / 2 ^ 90))

def fpUpper : ℚ :=
  (∑ j ∈ Finset.range 48, (j + 1) * vz ^ j / (2 * (j + 1) + 1)) +
    vz ^ 48 / (2 * (1 - vz))

def approximationBudget : ℚ := 323661607720025115242513 / 10 ^ 24
def zBound : ℚ :=
  (2 * ray / q100) / (1 - (((Sc : ℚ) - m0) / ((Sc : ℚ) + m0)) ^ 2)
def uBound : ℚ := 2 * ray * a * fpUpper / 2 ^ 96
def hornerBound : ℚ :=
  2 * ray * a *
    (p * dError u0 + pError u0 * d) / (d * (d + dError u0))
def closingDivisionBound : ℚ := 2 * ray / q100

def total : ℚ :=
  approximationBudget + zBound + uBound + hornerBound + closingDivisionBound

def coreNum : Nat := 32886404036042980977667
def coreDen : Nat := 10 ^ 23

theorem total_lt_core : total < coreNum / coreDen := by
  decide +kernel

end LnFloorCarry.Arithmetic

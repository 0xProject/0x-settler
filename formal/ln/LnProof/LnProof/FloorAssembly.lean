import LnProof.FloorCaps
import LnProof.FloorBudget
import LnProof.FloorModel

/-!
# Floor-spec assembly: scale identities

`model_floor_bracket` brackets the model output `r` against the pre-shift
accumulator `V = X1·5^27 + ln2k + BIAS` at scale `2^72`. The caps live at
scale `QS = 10^27·2^99`, reached by multiplying `V` by `2^27`. This file
provides the exact decomposition of `V·2^27` into the three cap exponents
on each `clz` side.
-/

namespace LnFloorCert
open LnGeneratedModel LnPoly LnExp LnFloor

/-- `V·2^27` splits into the three cap exponents (positive binade shift). -/
theorem v_scale_pos (X1v : Int) (c : Nat) (hc : c ≤ 152) :
    (X1v * 7450580596923828125 + ln2kInt c +
        143060321855302967919159136223863753677754092301269) * 2 ^ 27 =
      X1v * 1000000000000000000000000000 +
        ((152 - c : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) +
        143060321855302967919159136223863753677754092301269 * 2 ^ 27 := by
  have hl : ln2kInt c = (LN2c : Int) * ((152 - c : Nat) : Int) := by
    unfold ln2kInt
    rw [if_pos hc]
  rw [hl, Int.add_mul, Int.add_mul, Int.mul_assoc,
    show (7450580596923828125 : Int) * 2 ^ 27 =
      1000000000000000000000000000 from by decide]
  have e : (LN2c : Int) * ((152 - c : Nat) : Int) * 2 ^ 27 =
      ((152 - c : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [e]

/-- `V·2^27` splits with the `ln 2` term on the other side (negative shift). -/
theorem v_scale_neg (X1v : Int) (c : Nat) (hc : 152 < c) :
    (X1v * 7450580596923828125 + ln2kInt c +
        143060321855302967919159136223863753677754092301269) * 2 ^ 27 +
        ((c - 152 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) =
      X1v * 1000000000000000000000000000 +
        143060321855302967919159136223863753677754092301269 * 2 ^ 27 := by
  have hl : ln2kInt c = -((LN2c : Int) * ((c - 152 : Nat) : Int)) := by
    unfold ln2kInt
    rw [if_neg (by omega)]
  rw [hl, Int.add_mul, Int.add_mul, Int.mul_assoc,
    show (7450580596923828125 : Int) * 2 ^ 27 =
      1000000000000000000000000000 from by decide]
  have e : -((LN2c : Int) * ((c - 152 : Nat) : Int)) * 2 ^ 27 +
      ((c - 152 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = 0 := by
    have e1 : (LN2c : Int) * ((c - 152 : Nat) : Int) * 2 ^ 27 =
        ((c - 152 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    rw [Int.neg_mul, e1]
    omega
  generalize hgA : X1v * 1000000000000000000000000000 = A at *
  generalize hgL : -((LN2c : Int) * ((c - 152 : Nat) : Int)) * 2 ^ 27 = L1 at *
  generalize hgL2 : ((c - 152 : Nat) : Int) * ((LN2c : Int) * 2 ^ 27) = L2 at *
  omega

end LnFloorCert

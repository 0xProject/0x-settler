import Common.Foundation.ExpSum
import LnProof.Model.Body
import LnProof.Spec.Cut

open FormalYul
open FormalYul.Preservation

/-!
# Constant-piece caps for the strict-margin bound

Every exponent in the floor-specification assembly is an integer multiple
of `1/(10^27 2^99)`: the model's quotient contributes `X1/2^99`, the
exponent word contributes `k LN2c/(2^72 10^27)`, and the bias contributes
`BIASc/(2^72 10^27)`. The strict-margin bound uses two-sided caps for the
scaled `ln 2` piece, a lower cap for the bias, and a lower cap for one output
ulp. Each cap is pinned by a kernel-checked partial sum; upper caps also carry
the geometric tail.
-/

set_option maxRecDepth 8192

namespace LnFloor

open Common.Exp LnYul

/-- `e^(LN2c 2^27 / QS) ≤ 2 (1 + 1e-40)`: the scaled `ln 2` constant. -/
theorem cap2U : capUB (LN2c * 2 ^ 27) QS (2 * (10 ^ 40 + 1)) (10 ^ 40) := by
  refine capUB_of_partial (K := 40) QS_pos (by decide) ?_
  decide

/-- `e^(LN2c 2^27 / QS) ≥ 2 (1 - 1e-40)`. -/
theorem cap2L : capLB (LN2c * 2 ^ 27) QS (2 * (10 ^ 40 - 1)) (10 ^ 40) :=
  ⟨40, by decide⟩

/-- `e^(BIASc 2^27 / QS) ≥ (S/10^18)(1 - 3.404e-28)`. -/
theorem capBL : capLB (BIASc * 2 ^ 27) QS (Sc * (10 ^ 31 - 3384))
    (10 ^ 18 * 10 ^ 31) :=
  ⟨130, by decide⟩

/-- `e^(2^99/QS) = e^(1e-27) ≥ 1 + 0.999e-27`: one output ulp. -/
theorem capEL : capLB (2 ^ 99) QS (10 ^ 31 + 9990) (10 ^ 31) :=
  ⟨3, by decide⟩

/-- Exact signed value of the `ln2 * k` word for every `clz` value. -/
def ln2kExact (c : Nat) : Bool :=
  decide (int256 (evmMul LN2c (evmSub 160 c)) =
    if c ≤ 160 then (LN2c : Int) * ((160 - c : Nat) : Int)
    else -((LN2c : Int) * ((c - 160 : Nat) : Int)))

theorem ln2k_exact_all : (List.range 256).all ln2kExact = true := by decide

theorem ln2k_exact {c : Nat} (hc : c < 256) :
    int256 (evmMul LN2c (evmSub 160 c)) =
      if c ≤ 160 then (LN2c : Int) * ((160 - c : Nat) : Int)
      else -((LN2c : Int) * ((c - 160 : Nat) : Int)) := by
  have h := ln2k_exact_all
  rw [List.all_eq_true] at h
  have hm := h c (List.mem_range.mpr hc)
  rw [ln2kExact, decide_eq_true_eq] at hm
  exact hm

end LnFloor

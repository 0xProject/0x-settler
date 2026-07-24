import Common.Foundation.ExpSum

/-!
# Per-exponent budget inequalities

The floor-spec assembly multiplies the lower `X1` caps with the `2^k`
caps, the bias caps, and one output ulp, then weakens the resulting
rational to the `x/10^18` target through the mantissa window. The four
remaining integer inequalities cover nonnegative and negative binade
shifts for the direct and reciprocal branches.

Also provides `capLB_cancel`, the lower mirror of `capUB_cancel`, used
to move the `2^|k|` factor across the quotient when `k < 0`.
-/

namespace Common.Exp

/-- `e^(pa/q) = e^((pa+pb)/q) / e^(pb/q) ≥ (C/W) / (G/V)`. -/
theorem capLB_cancel {pa pb q C W G V : Nat} (hq : 0 < q)
    (hsum : capLB (pa + pb) q C W) (hb : capUB pb q G V) :
    capLB pa q (C * V) (W * G) := by
  obtain ⟨n, hn⟩ := hsum
  refine ⟨n, ?_⟩
  have hd : 0 < fact n * q ^ n := mul_pos' (fact_pos n) (Nat.pow_pos hq)
  refine Nat.le_of_mul_le_mul_right ?_ hd
  calc (C * V) * (fact n * q ^ n) * (fact n * q ^ n)
      = (C * (fact n * q ^ n)) * (V * (fact n * q ^ n)) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ (expNum n (pa + pb) q * W) * (V * (fact n * q ^ n)) :=
        Nat.mul_le_mul_right _ hn
    _ = (expNum n (pa + pb) q * (fact n * q ^ n)) * V * W := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ (expNum n pa q * expNum n pb q) * V * W :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (sum_le_prod n pa pb q))
    _ = (expNum n pb q * V) * (expNum n pa q * W) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ (G * (fact n * q ^ n)) * (expNum n pa q * W) :=
        Nat.mul_le_mul_right _ (hb n)
    _ = expNum n pa q * (W * G) * (fact n * q ^ n) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

end Common.Exp

namespace LnFloorCert

/-- Lower weakening budget, `k ≥ 0` (worst case `x = (m+1) 2^k`, `m = 2^95`). -/
def budgetL (k : Nat) : Bool :=
  decide ((2 ^ 95 + 1) * 2 ^ k * (10 ^ 40 : Nat) ^ k * 10 ^ 142 ≤
    2 ^ 95 * (10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ k * (10 ^ 31 - 3384) *
      (10 ^ 31 + 9990) * (10 ^ 31 - 10) * 10 ^ 18)

/-- Lower weakening budget, `k < 0` (exact mantissa). -/
def budgetLn (j : Nat) : Bool :=
  decide ((10 : Nat) ^ 142 * (2 * (10 ^ 40 + 1)) ^ j ≤
    2 ^ j * (10 ^ 40 : Nat) ^ j * (10 ^ 31 - 3385) * (10 ^ 31 - 3384) *
      (10 ^ 31 + 9990) * (10 ^ 31 - 10) * 10 ^ 18)

theorem budgetL_all : (List.range 160).all budgetL = true := by
  decide +kernel

theorem budgetLn_all : (List.range 96).all budgetLn = true := by
  decide +kernel

theorem budgetL_le {k : Nat} (hk : k ≤ 159) :
    (2 ^ 95 + 1) * 2 ^ k * (10 ^ 40 : Nat) ^ k * 10 ^ 142 ≤
      2 ^ 95 * (10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ k * (10 ^ 31 - 3384) *
        (10 ^ 31 + 9990) * (10 ^ 31 - 10) * 10 ^ 18 := by
  have h := List.all_eq_true.mp budgetL_all k (List.mem_range.mpr (by omega))
  simp only [budgetL, decide_eq_true_eq] at h
  exact h

theorem budgetLn_le {j : Nat} (hj : j ≤ 95) :
    (10 : Nat) ^ 142 * (2 * (10 ^ 40 + 1)) ^ j ≤
      2 ^ j * (10 ^ 40 : Nat) ^ j * (10 ^ 31 - 3385) * (10 ^ 31 - 3384) *
        (10 ^ 31 + 9990) * (10 ^ 31 - 10) * 10 ^ 18 := by
  have h := List.all_eq_true.mp budgetLn_all j (List.mem_range.mpr (by omega))
  simp only [budgetLn, decide_eq_true_eq] at h
  exact h

/-- Reciprocal-side strict budget, `k ≥ 0` (worst case `x = (m+1)·2^k`,
`m = 2^95`), for the `r + 2 ≤ 0` B-atom. -/
def budgetB (k : Nat) : Bool :=
  decide ((10 : Nat) ^ 31 * (10 ^ 40 : Nat) ^ k * (10 ^ 18 * 10 ^ 31) * 10 ^ 31 *
      ((2 ^ 95 + 1) * 2 ^ k) * 10 ^ 31 ≤
    10 ^ 18 * (10 ^ 31 - 10) * 2 ^ 95 * (10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ k *
      (10 ^ 31 - 3384) * (10 ^ 31 + 9990))

/-- Reciprocal-side strict budget, `k < 0` (exact mantissa). -/
def budgetBn (j : Nat) : Bool :=
  decide ((2 * (10 ^ 40 + 1)) ^ j * (10 : Nat) ^ 31 * (10 ^ 18 * 10 ^ 31) * 10 ^ 31 *
      10 ^ 31 ≤
    10 ^ 18 * (10 ^ 31 - 10) * (10 ^ 40 : Nat) ^ j * 2 ^ j * (10 ^ 31 - 3385) *
      (10 ^ 31 - 3384) * (10 ^ 31 + 9990))

theorem budgetB_all : (List.range 160).all budgetB = true := by
  decide +kernel

theorem budgetBn_all : (List.range 96).all budgetBn = true := by
  decide +kernel

theorem budgetB_le {k : Nat} (hk : k ≤ 159) :
    (10 : Nat) ^ 31 * (10 ^ 40 : Nat) ^ k * (10 ^ 18 * 10 ^ 31) * 10 ^ 31 *
      ((2 ^ 95 + 1) * 2 ^ k) * 10 ^ 31 ≤
    10 ^ 18 * (10 ^ 31 - 10) * 2 ^ 95 * (10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ k *
      (10 ^ 31 - 3384) * (10 ^ 31 + 9990) := by
  have h := List.all_eq_true.mp budgetB_all k (List.mem_range.mpr (by omega))
  simp only [budgetB, decide_eq_true_eq] at h
  exact h

theorem budgetBn_le {j : Nat} (hj : j ≤ 95) :
    (2 * (10 ^ 40 + 1)) ^ j * (10 : Nat) ^ 31 * (10 ^ 18 * 10 ^ 31) * 10 ^ 31 *
      10 ^ 31 ≤
    10 ^ 18 * (10 ^ 31 - 10) * (10 ^ 40 : Nat) ^ j * 2 ^ j * (10 ^ 31 - 3385) *
      (10 ^ 31 - 3384) * (10 ^ 31 + 9990) := by
  have h := List.all_eq_true.mp budgetBn_all j (List.mem_range.mpr (by omega))
  simp only [budgetBn, decide_eq_true_eq] at h
  exact h

end LnFloorCert

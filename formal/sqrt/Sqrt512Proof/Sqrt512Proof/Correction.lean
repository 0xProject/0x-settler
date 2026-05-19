/-
  Correction step for 512-bit square root.

  After Karatsuba, r in {natSqrt(x), natSqrt(x) + 1}.
  Checking x < r^2 and decrementing gives exactly natSqrt(x).
-/
import SqrtProof.SqrtCorrect

/-- If natSqrt(x) <= r <= natSqrt(x) + 1, then
    (if x < r^2 then r-1 else r) = natSqrt(x). -/
theorem correction_correct (x r : Nat)
    (hlo : natSqrt x ≤ r) (hhi : r ≤ natSqrt x + 1) :
    (if x < r * r then r - 1 else r) = natSqrt x := by
  have hmlo : natSqrt x * natSqrt x ≤ x := natSqrt_sq_le x
  have hmhi : x < (natSqrt x + 1) * (natSqrt x + 1) := natSqrt_lt_succ_sq x
  -- r is either natSqrt x or natSqrt x + 1
  have hrm : r = natSqrt x ∨ r = natSqrt x + 1 := by omega
  rcases hrm with rfl | rfl
  · -- r = natSqrt x: (natSqrt x)^2 <= x so not (x < (natSqrt x)^2)
    simp [Nat.not_lt.mpr hmlo]
  · -- r = natSqrt x + 1: x < (natSqrt x + 1)^2, so decrement
    simp [hmhi]

/-- Correction produces the natSqrt spec. -/
theorem correction_spec (x r : Nat)
    (hlo : natSqrt x ≤ r) (hhi : r ≤ natSqrt x + 1) :
    let r' := if x < r * r then r - 1 else r
    r' * r' ≤ x ∧ x < (r' + 1) * (r' + 1) := by
  have h := correction_correct x r hlo hhi
  intro r'
  -- r' = natSqrt x
  have hr'_eq : r' = natSqrt x := h
  rw [hr'_eq]
  exact ⟨natSqrt_sq_le x, natSqrt_lt_succ_sq x⟩

/-- From the Karatsuba identity x + q^2 = r^2 + rem*H + x_lo_lo,
    x < r^2 <-> rem*H + x_lo_lo < q^2. -/
theorem correction_equiv (x q r rem_H x_lo_lo : Nat)
    (hident : x + q * q = r * r + rem_H + x_lo_lo) :
    (x < r * r) ↔ (rem_H + x_lo_lo < q * q) := by omega

import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open scoped BigOperators

namespace LnFloorCarry

open Finset

noncomputable section

theorem series_le_partial_geometric {v : Real} (hv0 : 0 ≤ v) (hv1 : v < 1)
    (N : Nat) :
    (∑' j : Nat, v ^ j / (2 * j + 1)) ≤
      (∑ j ∈ range N, v ^ j / (2 * j + 1)) +
        v ^ N / ((2 * N + 1) * (1 - v)) := by
  have hgeom : Summable (fun j : Nat => v ^ j) :=
    summable_geometric_of_lt_one hv0 hv1
  have hseries : Summable (fun j : Nat => v ^ j / (2 * j + 1)) :=
    hgeom.of_nonneg_of_le
      (fun j => div_nonneg (pow_nonneg hv0 j) (by positivity))
      (fun j => div_le_self (pow_nonneg hv0 j) (by
        have hj : (0 : Real) ≤ j := Nat.cast_nonneg j
        linarith))
  have htail : Summable (fun j : Nat => v ^ (j + N) / (2 * (j + N) + 1)) :=
    by simpa only [Nat.cast_add] using (summable_nat_add_iff N).2 hseries
  have htailGeom : Summable (fun j : Nat =>
      (v ^ N / (2 * N + 1)) * v ^ j) :=
    hgeom.mul_left (v ^ N / (2 * N + 1))
  have htailLe :
      (∑' j : Nat, v ^ (j + N) / (2 * (j + N) + 1)) ≤
        ∑' j : Nat, (v ^ N / (2 * N + 1)) * v ^ j := by
    apply htail.tsum_le_tsum _ htailGeom
    intro j
    have hden : (0 : Real) < 2 * N + 1 := by positivity
    have hdenLe : (2 * N + 1 : Real) ≤ 2 * (j + N) + 1 := by
      have hj0 : (0 : Real) ≤ j := Nat.cast_nonneg j
      linarith
    have hpow : v ^ (j + N) = v ^ N * v ^ j := by
      rw [pow_add, mul_comm]
    rw [hpow]
    have hnum : 0 ≤ v ^ N * v ^ j :=
      mul_nonneg (pow_nonneg hv0 _) (pow_nonneg hv0 _)
    calc
      _ ≤ v ^ N * v ^ j / (2 * N + 1) :=
        div_le_div_of_nonneg_left hnum hden hdenLe
      _ = (v ^ N / (2 * N + 1)) * v ^ j := by ring
  rw [← hseries.sum_add_tsum_nat_add N]
  simp only [Nat.cast_add]
  calc
    (∑ j ∈ range N, v ^ j / (2 * j + 1)) +
          ∑' j : Nat, v ^ (j + N) / (2 * (j + N) + 1)
        ≤ (∑ j ∈ range N, v ^ j / (2 * j + 1)) +
            ∑' j : Nat, (v ^ N / (2 * N + 1)) * v ^ j :=
      add_le_add_left htailLe _
    _ = (∑ j ∈ range N, v ^ j / (2 * j + 1)) +
        v ^ N / ((2 * N + 1) * (1 - v)) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hv0 hv1]
      field_simp [show (1 : Real) - v ≠ 0 by linarith]

theorem partial_le_series {v : Real} (hv0 : 0 ≤ v) (hv1 : v < 1) (N : Nat) :
    (∑ j ∈ range N, v ^ j / (2 * j + 1)) ≤
      ∑' j : Nat, v ^ j / (2 * j + 1) := by
  have hgeom : Summable (fun j : Nat => v ^ j) :=
    summable_geometric_of_lt_one hv0 hv1
  have hseries : Summable (fun j : Nat => v ^ j / (2 * j + 1)) :=
    hgeom.of_nonneg_of_le
      (fun j => div_nonneg (pow_nonneg hv0 j) (by positivity))
      (fun j => div_le_self (pow_nonneg hv0 j) (by
        have hj : (0 : Real) ≤ j := Nat.cast_nonneg j
        linarith))
  exact hseries.sum_le_tsum (range N) (fun j _ => by positivity)

theorem neg_log_ratio_eq_log_sub_log {m S : Real} (hm : 0 < m) (hmS : m ≤ S) :
    -Real.log (m / S) =
      Real.log (1 + (S - m) / (S + m)) - Real.log (1 - (S - m) / (S + m)) := by
  have hS : 0 < S := lt_of_lt_of_le hm hmS
  have hden : 0 < S + m := add_pos hS hm
  have hplus : 1 + (S - m) / (S + m) = 2 * S / (S + m) := by
    field_simp [hden.ne']
    ring
  have hminus : 1 - (S - m) / (S + m) = 2 * m / (S + m) := by
    field_simp [hden.ne']
    ring
  have hplus0 : 1 + (S - m) / (S + m) ≠ 0 := by rw [hplus]; positivity
  have hminus0 : 1 - (S - m) / (S + m) ≠ 0 := by rw [hminus]; positivity
  symm
  calc
    Real.log (1 + (S - m) / (S + m)) - Real.log (1 - (S - m) / (S + m)) =
        Real.log ((1 + (S - m) / (S + m)) / (1 - (S - m) / (S + m))) :=
      (Real.log_div hplus0 hminus0).symm
    _ = Real.log (S / m) := by
      rw [hplus, hminus]
      congr 1
      field_simp [hm.ne', hS.ne', hden.ne']
      ring
    _ = Real.log ((m / S)⁻¹) := by
      congr 1
      field_simp [hm.ne', hS.ne']
    _ = -Real.log (m / S) := Real.log_inv _

theorem log_ratio_eq_log_sub_log {m S : Real} (hS : 0 < S) (hSm : S ≤ m) :
    Real.log (m / S) =
      Real.log (1 + (m - S) / (m + S)) - Real.log (1 - (m - S) / (m + S)) := by
  have hm : 0 < m := lt_of_lt_of_le hS hSm
  have hden : 0 < m + S := add_pos hm hS
  have hplus : 1 + (m - S) / (m + S) = 2 * m / (m + S) := by
    field_simp [hden.ne']
    ring
  have hminus : 1 - (m - S) / (m + S) = 2 * S / (m + S) := by
    field_simp [hden.ne']
    ring
  have hplus0 : 1 + (m - S) / (m + S) ≠ 0 := by rw [hplus]; positivity
  have hminus0 : 1 - (m - S) / (m + S) ≠ 0 := by rw [hminus]; positivity
  calc
    Real.log (m / S) =
        Real.log ((1 + (m - S) / (m + S)) / (1 - (m - S) / (m + S))) := by
      congr 1
      rw [hplus, hminus]
      field_simp [hm.ne', hS.ne', hden.ne']
      ring
    _ = Real.log (1 + (m - S) / (m + S)) - Real.log (1 - (m - S) / (m + S)) :=
      Real.log_div hplus0 hminus0

end

end LnFloorCarry

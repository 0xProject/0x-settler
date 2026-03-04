/-
  Denormalization: shifting the 512-bit cbrt result preserves ±1 accuracy.

  After normalizing x ↦ x_norm = x * 2^(3*shift), computing r_norm ≈ icbrt(x_norm)
  within 1 ulp, and de-normalizing via r = r_norm / 2^shift, we show:
    icbrt(x) ≤ r ≤ icbrt(x) + 1
  plus the overshoot property transfer.
-/
import CbrtProof.CbrtCorrect

namespace Cbrt512Spec

-- ============================================================================
-- Cube factoring through 2^(3k)
-- ============================================================================

/-- (a * b)³ = a³ * b³. -/
private theorem cube_mul (a b : Nat) :
    (a * b) * (a * b) * (a * b) = a * a * a * (b * b * b) := by
  suffices hi : (↑((a * b) * (a * b) * (a * b)) : Int) =
      ↑(a * a * a * (b * b * b)) by exact_mod_cast hi
  push_cast
  simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

/-- (a * 2^k)³ = a³ * 2^(3k). -/
private theorem cube_mul_pow (a k : Nat) :
    (a * 2 ^ k) * (a * 2 ^ k) * (a * 2 ^ k) = a * a * a * 2 ^ (3 * k) := by
  rw [cube_mul, show 2 ^ k * 2 ^ k * 2 ^ k = 2 ^ (3 * k) from by
    rw [show 3 * k = k + k + k from by omega, Nat.pow_add, Nat.pow_add]]

-- ============================================================================
-- icbrt(x_norm) range in terms of icbrt(x)
-- ============================================================================

/-- m * 2^k ≤ icbrt(x * 2^(3k)) where m = icbrt(x). -/
theorem icbrt_norm_lower (x k : Nat) :
    icbrt x * 2 ^ k ≤ icbrt (x * 2 ^ (3 * k)) := by
  have h : (icbrt x * 2 ^ k) * (icbrt x * 2 ^ k) * (icbrt x * 2 ^ k) ≤
      x * 2 ^ (3 * k) := by
    rw [cube_mul_pow]; exact Nat.mul_le_mul_right _ (icbrt_cube_le x)
  -- icbrt x * 2^k is a candidate lower bound for icbrt(x * 2^(3k))
  -- Use icbrt_eq_of_bounds indirectly: any n with n³ ≤ x_norm satisfies n ≤ icbrt(x_norm)
  by_cases hge : icbrt x * 2 ^ k ≤ icbrt (x * 2 ^ (3 * k))
  · exact hge
  · exfalso
    have hlt : icbrt (x * 2 ^ (3 * k)) < icbrt x * 2 ^ k := Nat.not_le.mp hge
    have h1 : icbrt (x * 2 ^ (3 * k)) + 1 ≤ icbrt x * 2 ^ k := hlt
    have h2 : (icbrt (x * 2 ^ (3 * k)) + 1) * (icbrt (x * 2 ^ (3 * k)) + 1) *
        (icbrt (x * 2 ^ (3 * k)) + 1) ≤
        (icbrt x * 2 ^ k) * (icbrt x * 2 ^ k) * (icbrt x * 2 ^ k) :=
      cube_monotone h1
    have h3 := icbrt_lt_succ_cube (x * 2 ^ (3 * k))
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h3 (Nat.le_trans h2 h))

/-- icbrt(x * 2^(3k)) < (icbrt(x) + 1) * 2^k. -/
theorem icbrt_norm_upper (x k : Nat) :
    icbrt (x * 2 ^ (3 * k)) < (icbrt x + 1) * 2 ^ k := by
  by_cases h : icbrt (x * 2 ^ (3 * k)) < (icbrt x + 1) * 2 ^ k
  · exact h
  · exfalso
    have hge : (icbrt x + 1) * 2 ^ k ≤ icbrt (x * 2 ^ (3 * k)) := Nat.not_lt.mp h
    have hcube_ge := cube_monotone hge
    have hle := icbrt_cube_le (x * 2 ^ (3 * k))
    have hlt : x * 2 ^ (3 * k) <
        (icbrt x + 1) * (icbrt x + 1) * (icbrt x + 1) * 2 ^ (3 * k) :=
      Nat.mul_lt_mul_of_pos_right (icbrt_lt_succ_cube x) (Nat.two_pow_pos _)
    rw [cube_mul_pow] at hcube_ge
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt (Nat.le_trans hcube_ge hle))

-- ============================================================================
-- Within-1-ulp denormalization
-- ============================================================================

/-- If icbrt(x_norm) ≤ r ≤ icbrt(x_norm) + 1 where x_norm = x * 2^(3k),
    then icbrt(x) ≤ r / 2^k ≤ icbrt(x) + 1. -/
theorem within_1ulp_denorm (x k r : Nat)
    (hlo : icbrt (x * 2 ^ (3 * k)) ≤ r)
    (hhi : r ≤ icbrt (x * 2 ^ (3 * k)) + 1) :
    icbrt x ≤ r / 2 ^ k ∧ r / 2 ^ k ≤ icbrt x + 1 := by
  have hpk : 0 < 2 ^ k := Nat.two_pow_pos k
  have h_norm_lo := icbrt_norm_lower x k
  have h_norm_hi := icbrt_norm_upper x k
  constructor
  · -- icbrt(x) ≤ r / 2^k
    exact (Nat.le_div_iff_mul_le hpk).mpr (Nat.le_trans h_norm_lo hlo)
  · -- r / 2^k ≤ icbrt(x) + 1
    -- r ≤ icbrt(x_norm) + 1 and icbrt(x_norm) < (icbrt(x)+1)*2^k
    -- so r < (icbrt(x)+1)*2^k + 1 ≤ (icbrt(x)+2)*2^k
    -- hence r / 2^k < icbrt(x)+2, i.e., r / 2^k ≤ icbrt(x)+1
    have hr_lt : r < (icbrt x + 2) * 2 ^ k := by
      have h1 : r ≤ icbrt (x * 2 ^ (3 * k)) + 1 := hhi
      have h2 : icbrt (x * 2 ^ (3 * k)) + 1 ≤ (icbrt x + 1) * 2 ^ k := h_norm_hi
      have h3 : (icbrt x + 1) * 2 ^ k < (icbrt x + 2) * 2 ^ k := by
        exact Nat.mul_lt_mul_of_pos_right (by omega) hpk
      omega
    exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hpk).mpr hr_lt)

-- ============================================================================
-- Overshoot transfer
-- ============================================================================

/-- If x_norm = x * 2^(3k) is not a perfect cube, then x is not either. -/
theorem overshoot_denorm (x k : Nat)
    (h_not_perfect_norm :
      icbrt (x * 2 ^ (3 * k)) * icbrt (x * 2 ^ (3 * k)) * icbrt (x * 2 ^ (3 * k)) <
        x * 2 ^ (3 * k)) :
    icbrt x * icbrt x * icbrt x < x := by
  by_cases h : icbrt x * icbrt x * icbrt x = x
  · exfalso
    -- If x is a perfect cube m³ = x, then (m * 2^k)³ = x * 2^(3k)
    let m := icbrt x
    have hcube : (m * 2 ^ k) * (m * 2 ^ k) * (m * 2 ^ k) = x * 2 ^ (3 * k) := by
      rw [cube_mul_pow, h]
    -- (m*2^k)³ ≤ x_norm so m*2^k ≤ icbrt(x_norm)
    -- Also icbrt(x_norm) < (m+1)*2^k, so icbrt(x_norm)³ < ((m+1)*2^k)³ = (m+1)³ * 2^(3k)
    -- But icbrt(x_norm)³ ≤ x_norm = m³ * 2^(3k) < (m+1)³ * 2^(3k)
    -- Combined with m*2^k ≤ icbrt(x_norm) < (m+1)*2^k
    -- Since (m*2^k)³ = x_norm, any n > m*2^k has n³ > x_norm, so icbrt(x_norm) = m*2^k.
    -- (m*2^k)³ = x_norm, and icbrt(x_norm) = m*2^k by uniqueness
    -- Need: x_norm < (m*2^k + 1)³
    have hsucc_cube : x * 2 ^ (3 * k) <
        (m * 2 ^ k + 1) * (m * 2 ^ k + 1) * (m * 2 ^ k + 1) := by
      rw [← hcube]
      let n := m * 2 ^ k
      show n * n * n < (n + 1) * (n + 1) * (n + 1)
      -- (n+1)³ - n³ = 3n² + 3n + 1 > 0
      -- (n+1)³ = n³ + 3n² + 3n + 1 > n³
      have hnn : n * n * n < n * n * n + (3 * (n * n) + 3 * n + 1) := by omega
      suffices heq : (n + 1) * (n + 1) * (n + 1) = n * n * n + (3 * (n * n) + 3 * n + 1) by
        rw [heq]; exact hnn
      suffices hi : (↑((n + 1) * (n + 1) * (n + 1)) : Int) =
          ↑(n * n * n + (3 * (n * n) + 3 * n + 1)) by exact_mod_cast hi
      push_cast; simp [Int.add_mul, Int.mul_add, Int.mul_one, Int.one_mul]; omega
    have hicbrt_eq := icbrt_eq_of_bounds (x * 2 ^ (3 * k)) (m * 2 ^ k)
      (Nat.le_of_eq hcube) hsucc_cube
    -- hicbrt_eq : m * 2^k = icbrt(x_norm)
    rw [← hicbrt_eq] at h_not_perfect_norm
    rw [hcube] at h_not_perfect_norm
    exact Nat.lt_irrefl _ h_not_perfect_norm
  · -- ¬(icbrt(x)³ = x) and icbrt(x)³ ≤ x implies icbrt(x)³ < x
    have hle := icbrt_cube_le x
    omega

end Cbrt512Spec

/-
  Lemma 1 (Floor Bound) for _sqrt convergence — Mathlib-free.
  For any m with m² ≤ x, and z > 0:  m ≤ (z + x / z) / 2
-/
import Init

/-- One Babylonian step: ⌊(z + ⌊x/z⌋) / 2⌋.
    Canonical definition used across the entire proof suite. -/
def bstep (x z : Nat) : Nat := (z + x / z) / 2

-- ============================================================================
-- Algebraic helpers
-- ============================================================================

/-- (a+b)² = b*(2a+b) + a² -/
private theorem sq_decomp_1 (a b : Nat) :
    (a + b) * (a + b) = b * (2 * a + b) + a * a := by
  rw [Nat.add_mul, Nat.mul_add a a b, Nat.mul_add b a b]
  rw [Nat.mul_add b (2 * a) b]
  rw [Nat.mul_comm b (2 * a), Nat.mul_assoc 2 a b, Nat.mul_comm a b]
  omega

/-- (a+b)*(a-b) + b² = a² for b ≤ a -/
private theorem sq_decomp_2 (a b : Nat) (h : b ≤ a) :
    (a + b) * (a - b) + b * b = a * a := by
  have hrecon : a - b + b = a := Nat.sub_add_cancel h
  rw [Nat.mul_comm (a + b) (a - b)]
  rw [Nat.mul_add (a - b) a b]
  -- ((a-b)*a + (a-b)*b) + b*b = a*a
  rw [Nat.add_assoc]
  -- (a-b)*a + ((a-b)*b + b*b) = a*a
  rw [← Nat.add_mul (a - b) b b, hrecon]
  -- (a-b)*a + a*b = a*a
  rw [Nat.mul_comm (a - b) a, ← Nat.mul_add a (a - b) b, hrecon]

-- ============================================================================
-- Core inequality: z * (2*m - z) ≤ m * m
-- ============================================================================

theorem sq_identity_le (z m : Nat) (h : z ≤ m) :
    z * (2 * m - z) + (m - z) * (m - z) = m * m := by
  have : 2 * m - z = 2 * (m - z) + z := by omega
  rw [this, ← sq_decomp_1 (m - z) z, Nat.sub_add_cancel h]

theorem sq_identity_ge (z m : Nat) (h1 : m ≤ z) (h2 : z ≤ 2 * m) :
    z * (2 * m - z) + (z - m) * (z - m) = m * m := by
  have key := sq_decomp_2 m (z - m) (by omega)
  have h3 : m + (z - m) = z := by omega
  have h4 : m - (z - m) = 2 * m - z := by omega
  rw [h3, h4] at key; exact key

theorem mul_two_sub_le_sq (z m : Nat) : z * (2 * m - z) ≤ m * m := by
  by_cases h : z ≤ m
  · have := sq_identity_le z m h; omega
  · simp only [Nat.not_le] at h
    by_cases h2 : z ≤ 2 * m
    · have := sq_identity_ge z m (Nat.le_of_lt h) h2; omega
    · simp only [Nat.not_le] at h2
      simp [Nat.sub_eq_zero_of_le (Nat.le_of_lt h2)]

-- ============================================================================
-- Division bound
-- ============================================================================

theorem two_mul_le_add_div_sq (m z : Nat) (hz : 0 < z) :
    2 * m ≤ z + m * m / z := by
  suffices h : 2 * m - z ≤ m * m / z by omega
  rw [Nat.le_div_iff_mul_le hz, Nat.mul_comm]
  exact mul_two_sub_le_sq z m

-- ============================================================================
-- MAIN THEOREM: Lemma 1 (Floor Bound)
-- ============================================================================

/--
**Lemma 1 (Floor Bound).**

For any `m` with `m * m ≤ x`, and `z > 0`:
    m ≤ (z + x / z) / 2

A single truncated Babylonian step never undershoots any `m` with `m² ≤ x`.
-/
theorem babylon_step_floor_bound (x z m : Nat) (hz : 0 < z) (hm : m * m ≤ x) :
    m ≤ (z + x / z) / 2 := by
  rw [Nat.le_div_iff_mul_le (by omega : (0 : Nat) < 2)]
  have h_mono : m * m / z ≤ x / z := Nat.div_le_div_right hm
  have h_core := two_mul_le_add_div_sq m z hz
  omega

-- ============================================================================
-- Lemma 2: Absorbing set {m, m+1}
-- ============================================================================

/-- (m+1)² = m² + 2m + 1 -/
private theorem succ_sq (m : Nat) :
    (m + 1) * (m + 1) = m * m + 2 * m + 1 := by
  rw [sq_decomp_1 m 1, Nat.one_mul]; omega

/-- (m-1)*(m+1) + 1 = m*m -/
private theorem pred_succ_sq (m : Nat) (hm : 0 < m) :
    (m - 1) * (m + 1) + 1 = m * m := by
  -- sq_decomp_2 m 1: (m+1)*(m-1) + 1*1 = m*m
  have key := sq_decomp_2 m 1 (by omega)
  rw [Nat.mul_comm (m + 1) (m - 1), Nat.mul_one] at key
  -- key: (m-1)*(m+1) + 1 = m*m
  exact key

/-- From z = m+1, one step gives m. -/
theorem babylon_from_ceil (x m : Nat) (hm : 0 < m)
    (hlo : m * m ≤ x) (hhi : x < (m + 1) * (m + 1)) :
    (m + 1 + x / (m + 1)) / 2 = m := by
  have hmp : 0 < m + 1 := by omega
  -- x/(m+1) ≤ m: since x < (m+1)², x/(m+1) < m+1, so x/(m+1) ≤ m
  have hd_hi : x / (m + 1) ≤ m := by
    have : x / (m + 1) < m + 1 := Nat.div_lt_of_lt_mul hhi
    omega
  -- x/(m+1) ≥ m-1
  have hd_lo : m - 1 ≤ x / (m + 1) := by
    rw [Nat.le_div_iff_mul_le hmp]
    have := pred_succ_sq m hm; omega
  omega

/-- From z = m, one step gives m or m+1. -/
theorem babylon_from_floor (x m : Nat) (hm : 0 < m)
    (hlo : m * m ≤ x) (hhi : x < (m + 1) * (m + 1)) :
    let z' := (m + x / m) / 2
    z' = m ∨ z' = m + 1 := by
  simp only
  -- x/m ≥ m
  have hd_lo : m ≤ x / m := by
    rw [Nat.le_div_iff_mul_le hm]; exact hlo
  -- x/m ≤ m+2: x < (m+1)² = m²+2m+1, so x ≤ m²+2m = (m+2)*m
  have hd_hi : x / m ≤ m + 2 := by
    have hsq := succ_sq m
    have hx_le : x ≤ m * m + 2 * m := by omega
    calc x / m
        ≤ (m * m + 2 * m) / m := Nat.div_le_div_right hx_le
      _ = (m + 2) * m / m := by rw [Nat.add_mul]
      _ = m + 2 := Nat.mul_div_cancel (m + 2) hm
  omega

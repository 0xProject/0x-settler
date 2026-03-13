/-
  Normalization lemma for 512-bit square root.

  Main theorem: natSqrt(x * 4^k) / 2^k = natSqrt(x)

  Justifies the even-shift normalize / un-normalize pattern in 512Math._sqrt.
-/
import SqrtProof.SqrtCorrect

-- ============================================================================
-- Part 1: Uniqueness of floor sqrt
-- ============================================================================

/-- If m^2 <= n < (m+1)^2, then natSqrt n = m. -/
theorem natSqrt_unique (n m : Nat)
    (hlo : m * m ≤ n) (hhi : n < (m + 1) * (m + 1)) :
    natSqrt n = m := by
  have ⟨hrlo, hrhi⟩ := natSqrt_spec n
  have hmr : m ≤ natSqrt n := by
    suffices h : ¬(natSqrt n < m) by omega
    intro h
    have h1 : natSqrt n + 1 ≤ m := h
    have h2 := Nat.mul_le_mul h1 h1
    omega
  have hrm : natSqrt n ≤ m := by
    suffices h : ¬(m < natSqrt n) by omega
    intro h
    have h1 : m + 1 ≤ natSqrt n := h
    have h2 := Nat.mul_le_mul h1 h1
    omega
  omega

-- ============================================================================
-- Part 2: Bracket for natSqrt of scaled value
-- ============================================================================

private theorem mul_sq (a b : Nat) : (a * b) * (a * b) = (a * a) * (b * b) := by
  calc (a * b) * (a * b)
      = a * (b * (a * b)) := by rw [Nat.mul_assoc]
    _ = a * (a * (b * b)) := by rw [Nat.mul_left_comm b a b]
    _ = (a * a) * (b * b) := by rw [Nat.mul_assoc]

theorem natSqrt_mul_sq_lower (x c : Nat) :
    natSqrt x * c ≤ natSqrt (x * (c * c)) := by
  by_cases hc : c = 0
  · simp [hc]
  · have hsq : (natSqrt x * c) * (natSqrt x * c) ≤ x * (c * c) := by
      rw [mul_sq]; exact Nat.mul_le_mul_right _ (natSqrt_sq_le x)
    suffices h : ¬(natSqrt (x * (c * c)) < natSqrt x * c) by omega
    intro h
    have h1 : natSqrt (x * (c * c)) + 1 ≤ natSqrt x * c := h
    have h2 := Nat.mul_le_mul h1 h1
    have h3 := natSqrt_lt_succ_sq (x * (c * c))
    omega

theorem natSqrt_mul_sq_upper (x c : Nat) (hc : 0 < c) :
    natSqrt (x * (c * c)) < (natSqrt x + 1) * c := by
  have hsq : x * (c * c) < ((natSqrt x + 1) * c) * ((natSqrt x + 1) * c) := by
    rw [mul_sq]
    exact Nat.mul_lt_mul_of_pos_right (natSqrt_lt_succ_sq x) (Nat.mul_pos hc hc)
  suffices h : ¬((natSqrt x + 1) * c ≤ natSqrt (x * (c * c))) by omega
  intro h
  have h2 := Nat.mul_le_mul h h
  have h3 := natSqrt_sq_le (x * (c * c))
  omega

-- ============================================================================
-- Part 3: Division theorem
-- ============================================================================

private theorem four_pow_eq (k : Nat) : 4 ^ k = 2 ^ k * 2 ^ k := by
  have : (4 : Nat) = 2 ^ 2 := by decide
  rw [this, ← Nat.pow_mul, ← Nat.pow_add]
  congr 1; omega

/-- natSqrt(x * 4^k) / 2^k = natSqrt(x). -/
theorem natSqrt_shift_div (x k : Nat) :
    natSqrt (x * 4 ^ k) / 2 ^ k = natSqrt x := by
  by_cases hk : k = 0
  · simp [hk]
  · have hpow : 0 < 2 ^ k := Nat.two_pow_pos k
    rw [four_pow_eq]
    have hlo := natSqrt_mul_sq_lower x (2 ^ k)
    have hhi := natSqrt_mul_sq_upper x (2 ^ k) hpow
    have h1 : natSqrt x ≤ natSqrt (x * (2 ^ k * 2 ^ k)) / 2 ^ k := by
      rw [Nat.le_div_iff_mul_le hpow]
      exact hlo
    have h2 : natSqrt (x * (2 ^ k * 2 ^ k)) / 2 ^ k < natSqrt x + 1 := by
      rw [Nat.div_lt_iff_lt_mul hpow]
      -- Need: natSqrt(x * (2^k * 2^k)) < (natSqrt x + 1) * 2^k
      -- hhi says exactly this
      exact hhi
    omega

-- ============================================================================
-- Part 4: Shift-range lemma
-- ============================================================================

private theorem four_pow_eq_two_pow (shift : Nat) : 4 ^ shift = 2 ^ (2 * shift) := by
  have : (4 : Nat) = 2 ^ 2 := by decide
  rw [this, ← Nat.pow_mul]

/-- After normalization, x_hi * 4^shift in [2^254, 2^256). -/
theorem shift_range (x_hi : Nat) (hlo : 0 < x_hi) (hhi : x_hi < 2 ^ 256) :
    let shift := (255 - Nat.log2 x_hi) / 2
    2 ^ 254 ≤ x_hi * 4 ^ shift ∧ x_hi * 4 ^ shift < 2 ^ 256 := by
  intro shift
  have hne : x_hi ≠ 0 := Nat.ne_of_gt hlo
  have hlog := (Nat.log2_eq_iff hne).1 rfl
  have hL : Nat.log2 x_hi ≤ 255 := by
    have := (Nat.log2_lt hne).2 hhi; omega
  have h2shift : 2 * shift ≤ 255 - Nat.log2 x_hi := Nat.mul_div_le (255 - Nat.log2 x_hi) 2
  have h2shift_lb : 255 - Nat.log2 x_hi < 2 * shift + 2 := by
    have h := Nat.div_add_mod (255 - Nat.log2 x_hi) 2
    have hmod : (255 - Nat.log2 x_hi) % 2 < 2 := Nat.mod_lt _ (by omega)
    omega
  rw [four_pow_eq_two_pow]
  constructor
  · calc 2 ^ 254
        ≤ 2 ^ (Nat.log2 x_hi + 2 * shift) := by
          apply Nat.pow_le_pow_right (by omega : 1 ≤ 2); omega
      _ = 2 ^ (Nat.log2 x_hi) * 2 ^ (2 * shift) := by rw [Nat.pow_add]
      _ ≤ x_hi * 2 ^ (2 * shift) := Nat.mul_le_mul_right _ hlog.1
  · calc x_hi * 2 ^ (2 * shift)
        < 2 ^ (Nat.log2 x_hi + 1) * 2 ^ (2 * shift) :=
          Nat.mul_lt_mul_of_pos_right hlog.2 (Nat.two_pow_pos _)
      _ = 2 ^ (Nat.log2 x_hi + 1 + 2 * shift) := by
          rw [← Nat.pow_add]
      _ ≤ 2 ^ 256 := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega)

/-
  Ceiling square root for 512-bit values.
  Models 512Math.osqrtUp (lines 1798-1811).
-/
import Sqrt512Proof.Sqrt512Correct

private theorem sq_expand_aux (m : Nat) :
    (m + 1) * (m + 1) = m * m + 2 * m + 1 := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.one_mul]
  -- Goal: m * m + m + (m + 1 * 1) = m * m + 2 * m + 1
  rw [Nat.one_mul]; omega

/-- 512-bit ceiling square root. -/
noncomputable def sqrtUp512 (x : Nat) : Nat :=
  let r := sqrt512 x
  if r * r < x then r + 1 else r

/-- sqrtUp512 is the ceiling sqrt: x <= r^2 and r is minimal. -/
theorem sqrtUp512_correct (x : Nat) (hx : x < 2 ^ 512) :
    let r := sqrtUp512 x
    x ≤ r * r ∧ ∀ y, x ≤ y * y → r ≤ y := by
  simp only
  have hsqrt := sqrt512_correct x hx
  have hs_lo : sqrt512 x * sqrt512 x ≤ x := by rw [hsqrt]; exact natSqrt_sq_le x
  have hs_hi : x < (sqrt512 x + 1) * (sqrt512 x + 1) := by rw [hsqrt]; exact natSqrt_lt_succ_sq x
  unfold sqrtUp512
  simp only
  by_cases hlt : sqrt512 x * sqrt512 x < x
  · -- s^2 < x: ceiling is s + 1
    simp [hlt]
    exact ⟨by omega, fun y hy => by
      suffices h : ¬(y < sqrt512 x + 1) by omega
      intro hc
      have hc' : y ≤ sqrt512 x := by omega
      have := Nat.mul_le_mul hc' hc'; omega⟩
  · -- s^2 = x: ceiling is s
    simp [hlt]
    have hseq : sqrt512 x * sqrt512 x = x := by omega
    exact ⟨by omega, fun y hy => by
      suffices h : ¬(y < sqrt512 x) by omega
      intro hc
      have hc' : y ≤ sqrt512 x - 1 := by omega
      have h1 := Nat.mul_le_mul hc' hc'
      -- y*y ≤ (s-1)*(s-1) and (s-1)*(s-1) < s*s = x
      -- (s-1)*(s-1) < s*s since (s-1+1)*(s-1+1) = (s-1)*(s-1) + 2*(s-1) + 1
      have h2 : 0 < sqrt512 x := by omega
      have h3 := sq_expand_aux (sqrt512 x - 1)
      -- h3 : (s-1+1)*(s-1+1) = (s-1)*(s-1) + 2*(s-1) + 1
      have h4 : (sqrt512 x - 1) + 1 = sqrt512 x := by omega
      rw [h4] at h3
      -- h3 : s*s = (s-1)*(s-1) + 2*(s-1) + 1
      -- so (s-1)*(s-1) = s*s - 2*(s-1) - 1 < s*s = x
      -- and y*y ≤ (s-1)*(s-1) < x, contradicting x ≤ y*y
      omega⟩

/-- sqrtUp512 satisfies the ceiling sqrt spec. -/
theorem sqrtUp512_spec (x : Nat) (hx : x < 2 ^ 512) :
    let r := sqrtUp512 x
    x ≤ r * r ∧ (r = 0 ∨ (r - 1) * (r - 1) < x) := by
  have ⟨h1, h2⟩ := sqrtUp512_correct x hx
  simp only at h1 h2 ⊢
  refine ⟨h1, ?_⟩
  by_cases hr0 : sqrtUp512 x = 0
  · left; exact hr0
  · right
    suffices h : ¬((sqrtUp512 x - 1) * (sqrtUp512 x - 1) ≥ x) by omega
    intro hc
    have := h2 (sqrtUp512 x - 1) hc
    omega

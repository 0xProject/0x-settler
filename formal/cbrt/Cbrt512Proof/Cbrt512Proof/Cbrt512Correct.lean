/-
  Ceiling cube root for 512-bit values.
  Models 512Math.cbrtUp.

  No separate `cbrt512` definition is needed because `icbrt` from CbrtCorrect.lean
  is already defined for all Nat (including values >= 2^256).
-/
import CbrtProof.CbrtCorrect

private theorem cube_expand_aux (m : Nat) :
    (m + 1) * (m + 1) * (m + 1) = m * m * m + 3 * m * m + 3 * m + 1 := by
  -- Prove in Int (where simp can normalize polynomial products) then cast back
  have key : (m + 1 : Int) * (m + 1) * (m + 1) = m * m * m + 3 * m * m + 3 * m + 1 := by
    have : (m + 1 : Int) * (m + 1) = m * m + 2 * m + 1 := by
      simp [Int.add_mul, Int.mul_add, Int.mul_one, Int.one_mul]; omega
    rw [this]
    simp [Int.add_mul, Int.mul_add, Int.mul_one, Int.one_mul, Int.mul_assoc]
    omega
  exact_mod_cast key

/-- 512-bit ceiling cube root. -/
noncomputable def cbrtUp512 (x : Nat) : Nat :=
  let r := icbrt x
  if r * r * r < x then r + 1 else r

/-- cbrtUp512 is the ceiling cbrt: x ≤ r³ and r is minimal. -/
theorem cbrtUp512_correct (x : Nat) (_hx : x < 2 ^ 512) :
    let r := cbrtUp512 x
    x ≤ r * r * r ∧ ∀ y, x ≤ y * y * y → r ≤ y := by
  simp only
  have hs_lo : icbrt x * icbrt x * icbrt x ≤ x := icbrt_cube_le x
  have hs_hi : x < (icbrt x + 1) * (icbrt x + 1) * (icbrt x + 1) := icbrt_lt_succ_cube x
  unfold cbrtUp512
  simp only
  by_cases hlt : icbrt x * icbrt x * icbrt x < x
  · -- s³ < x: ceiling is s + 1
    simp [hlt]
    exact ⟨by omega, fun y hy => by
      suffices h : ¬(y < icbrt x + 1) by omega
      intro hc
      have hc' : y ≤ icbrt x := by omega
      have := cube_monotone hc'; omega⟩
  · -- s³ = x: ceiling is s
    simp [hlt]
    have hseq : icbrt x * icbrt x * icbrt x = x := by omega
    exact ⟨by omega, fun y hy => by
      suffices h : ¬(y < icbrt x) by omega
      intro hc
      have hc' : y ≤ icbrt x - 1 := by omega
      have h1 := cube_monotone hc'
      have h2 : 0 < icbrt x := by omega
      have h3 := cube_expand_aux (icbrt x - 1)
      have h4 : (icbrt x - 1) + 1 = icbrt x := by omega
      rw [h4] at h3
      omega⟩

/-- cbrtUp512 satisfies the ceiling cbrt spec. -/
theorem cbrtUp512_spec (x : Nat) (hx : x < 2 ^ 512) :
    let r := cbrtUp512 x
    x ≤ r * r * r ∧ (r = 0 ∨ (r - 1) * (r - 1) * (r - 1) < x) := by
  have ⟨h1, h2⟩ := cbrtUp512_correct x hx
  simp only at h1 h2 ⊢
  refine ⟨h1, ?_⟩
  by_cases hr0 : cbrtUp512 x = 0
  · left; exact hr0
  · right
    suffices h : ¬((cbrtUp512 x - 1) * (cbrtUp512 x - 1) * (cbrtUp512 x - 1) ≥ x) by omega
    intro hc
    have := h2 (cbrtUp512 x - 1) hc
    omega

import ExpProof.Mono.MulTree

/-!
# `mulExpRay` value and panic domains

The runtime guard partitions canonical calldata into a value path and a `Panic(17)` path. The value
domain keeps the same short-circuits as the implementation: zero multiplier returns before any
range checks, sufficiently small exponents clamp to zero without needing the accuracy guard, and
the scale point is accepted independently of the `k ≤ s - 2` guard.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

/-- ABI words transported into this proof layer. -/
def MulExpRayCanonical (y x : Nat) : Prop :=
  y < 2 ^ 256 ∧ x < 2 ^ 256

/-- The exact successful-input domain induced by the implementation guard. -/
def MulExpRayValueDomain (y x : Nat) : Prop :=
  MulExpRayCanonical y x ∧
    (int256 y = 0 ∨
      absTree y ≤ scaleQ67 ∧
        int256 x < int256 xHiMulExpRay ∧
          (int256 x ≤ int256 xLoZeroMulExpRay ∨
            int256 x = 0 ∨
              int256 (kTree x) ≤ (scaleShiftTree (absTree y) : Int) - 2))

/-- The exact nonzero-multiplier panic domain induced by the implementation guard. -/
def MulExpRayPanicDomain (y x : Nat) : Prop :=
  MulExpRayCanonical y x ∧
    int256 y ≠ 0 ∧
      (scaleQ67 < absTree y ∨
        int256 xHiMulExpRay ≤ int256 x ∨
          (int256 x ≠ 0 ∧
            int256 xLoZeroMulExpRay < int256 x ∧
              (scaleShiftTree (absTree y) : Int) - 2 < int256 (kTree x)))

/-- Canonical inputs are either accepted by the value guard or rejected by the panic guard. -/
theorem mulExpRay_value_or_panic_of_canonical {y x : Nat} (hcanon : MulExpRayCanonical y x) :
    MulExpRayValueDomain y x ∨ MulExpRayPanicDomain y x := by
  by_cases hy0 : int256 y = 0
  · exact Or.inl ⟨hcanon, Or.inl hy0⟩
  · by_cases hscale : absTree y ≤ scaleQ67
    · by_cases hxhi : int256 x < int256 xHiMulExpRay
      · by_cases hxlo : int256 x ≤ int256 xLoZeroMulExpRay
        · exact Or.inl ⟨hcanon, Or.inr ⟨hscale, hxhi, Or.inl hxlo⟩⟩
        · by_cases hx0 : int256 x = 0
          · exact Or.inl ⟨hcanon, Or.inr ⟨hscale, hxhi, Or.inr (Or.inl hx0)⟩⟩
          · by_cases hk :
              int256 (kTree x) ≤ (scaleShiftTree (absTree y) : Int) - 2
            · exact Or.inl ⟨hcanon, Or.inr ⟨hscale, hxhi, Or.inr (Or.inr hk)⟩⟩
            · exact Or.inr ⟨hcanon, hy0,
                Or.inr (Or.inr ⟨hx0, by omega, by omega⟩)⟩
      · exact Or.inr ⟨hcanon, hy0, Or.inr (Or.inl (by omega))⟩
    · exact Or.inr ⟨hcanon, hy0, Or.inl (by omega)⟩

/-- The accepted and rejected guard domains are disjoint. -/
theorem mulExpRay_value_not_panic {y x : Nat} :
    MulExpRayValueDomain y x → ¬ MulExpRayPanicDomain y x := by
  intro hv hp
  rcases hv with ⟨_, hy0 | ⟨hscale, hxhi, hxlo | hx0 | hk⟩⟩
  · exact hp.2.1 hy0
  · rcases hp with ⟨_, _, hpguard⟩
    rcases hpguard with hbadScale | hbadHi | ⟨_, hbadLo, _⟩
    · omega
    · omega
    · omega
  · rcases hp with ⟨_, _, hpguard⟩
    rcases hpguard with hbadScale | hbadHi | ⟨hxne, _, _⟩
    · omega
    · omega
    · exact hxne hx0
  · rcases hp with ⟨_, _, hpguard⟩
    rcases hpguard with hbadScale | hbadHi | ⟨_, _, hbadK⟩
    · omega
    · omega
    · omega

/-- Canonical inputs are accepted exactly when they are not in the panic domain. -/
theorem mulExpRay_value_iff_not_panic {y x : Nat} (hcanon : MulExpRayCanonical y x) :
    MulExpRayValueDomain y x ↔ ¬ MulExpRayPanicDomain y x := by
  constructor
  · exact mulExpRay_value_not_panic
  · intro hnot
    rcases mulExpRay_value_or_panic_of_canonical hcanon with hval | hpanic
    · exact hval
    · exact False.elim (hnot hpanic)

end ExpYul

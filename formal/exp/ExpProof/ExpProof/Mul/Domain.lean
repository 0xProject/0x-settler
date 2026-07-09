import ExpProof.Mono.MulTree

/-!
# `mulExpRay` value and panic domains

The runtime guard partitions canonical calldata into a value path and a `Panic(17)` path. Every
multiplier takes the same guard: the magnitude bound, the unconditional upper fence at the first
octave past the deficit envelope, and the accuracy test on the closing shift — the latter waived
at the exact scale point `x = 0` and at or below the zero-clamp cutoff. Each predicate mirrors
one signed comparison of the compiled guard; `int256 (mulShiftTree y x) < 2` is exactly the
runtime's `slt(shift, 2)`.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation

/-- ABI words transported into this proof layer. -/
def MulExpRayCanonical (y x : Nat) : Prop :=
  y < 2 ^ 256 ∧ x < 2 ^ 256

/-- The exact successful-input domain induced by the implementation guard. -/
def MulExpRayValueDomain (y x : Nat) : Prop :=
  MulExpRayCanonical y x ∧
    absTree y ≤ scaleQ67 ∧
      int256 x < int256 mulExpRayHi ∧
        (int256 x = 0 ∨
          int256 x ≤ int256 mulExpRayZeroMax ∨
            2 ≤ int256 (mulShiftTree y x))

/-- The exact panic domain induced by the implementation guard. -/
def MulExpRayPanicDomain (y x : Nat) : Prop :=
  MulExpRayCanonical y x ∧
    (scaleQ67 < absTree y ∨
      int256 mulExpRayHi ≤ int256 x ∨
        (int256 x ≠ 0 ∧
          int256 mulExpRayZeroMax < int256 x ∧
            int256 (mulShiftTree y x) < 2))

/-- Canonical inputs are either accepted by the value guard or rejected by the panic guard. -/
theorem mulExpRay_value_or_panic_of_canonical {y x : Nat} (hcanon : MulExpRayCanonical y x) :
    MulExpRayValueDomain y x ∨ MulExpRayPanicDomain y x := by
  by_cases hscale : absTree y ≤ scaleQ67
  · by_cases hxhi : int256 x < int256 mulExpRayHi
    · by_cases hx0 : int256 x = 0
      · exact Or.inl ⟨hcanon, hscale, hxhi, Or.inl hx0⟩
      · by_cases hxlo : int256 x ≤ int256 mulExpRayZeroMax
        · exact Or.inl ⟨hcanon, hscale, hxhi, Or.inr (Or.inl hxlo)⟩
        · by_cases hshift : 2 ≤ int256 (mulShiftTree y x)
          · exact Or.inl ⟨hcanon, hscale, hxhi, Or.inr (Or.inr hshift)⟩
          · exact Or.inr ⟨hcanon, Or.inr (Or.inr ⟨hx0, by omega, by omega⟩)⟩
    · exact Or.inr ⟨hcanon, Or.inr (Or.inl (by omega))⟩
  · exact Or.inr ⟨hcanon, Or.inl (by omega)⟩

/-- The accepted and rejected guard domains are disjoint. -/
theorem mulExpRay_value_not_panic {y x : Nat} :
    MulExpRayValueDomain y x → ¬ MulExpRayPanicDomain y x := by
  intro hv hp
  obtain ⟨_, hscale, hxhi, hlive⟩ := hv
  obtain ⟨_, hbadScale | hbadHi | ⟨hxne, hbadLo, hbadShift⟩⟩ := hp
  · omega
  · omega
  · rcases hlive with hx0 | hxlo | hshift
    · exact hxne hx0
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

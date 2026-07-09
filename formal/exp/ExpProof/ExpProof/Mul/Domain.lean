import ExpProof.Mono.MulTree
import ExpProof.Mul.WordBridge

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


/-! ## The guard word as a decidable predicate -/

/-- The guard word is the `if`-encoding of the exact panic condition. -/
theorem mulExpGuardTree_eq_ite {y x : Nat} (hx : x < 2 ^ 256) :
    mulExpGuardTree y x =
      if scaleQ67 < absTree y ∨ int256 mulExpRayHi ≤ int256 x ∨
          (int256 x ≠ 0 ∧ int256 mulExpRayZeroMax < int256 x ∧
            int256 (mulShiftTree y x) < 2) then 1 else 0 := by
  have hux : u256 x = x := u256_of_lt_pow256 hx
  have hab : u256 (absTree y) = absTree y := u256_of_lt_pow256 (absTree_lt y)
  have hsh : u256 (mulShiftTree y x) = mulShiftTree y x :=
    u256_of_lt_pow256 (mulShiftTree_lt y x)
  have hhi : u256 mulExpRayHi = mulExpRayHi := u256_of_lt_pow256 mulExpRayHi_lt
  have hzm : u256 mulExpRayZeroMax = mulExpRayZeroMax := u256_of_lt_pow256 mulExpRayZeroMax_lt
  have hq : u256 scaleQ67 = scaleQ67 := u256_of_lt_pow256 (by unfold scaleQ67; norm_num)
  have h0 : u256 0 = 0 := u256_of_lt_pow256 (by norm_num)
  have h2 : u256 2 = 2 := u256_of_lt_pow256 (by norm_num)
  have hint2 : int256 (u256 2) = 2 := by rw [h2]; unfold int256; norm_num
  have hxz : (int256 (u256 x) = 0) = (int256 x = 0) := by rw [hux]
  unfold mulExpGuardTree
  rw [evmSgt_eq_evmSlt_swap, evmSlt_eq_ite x mulExpRayHi, evmSlt_eq_ite mulExpRayZeroMax x,
    evmSlt_eq_ite (mulShiftTree y x) 2, evmGt_eq_ite, evmEq_eq_ite]
  rw [hux, hab, hhi, hzm, hq, h0, hsh, hint2]
  rw [show (if x = (0 : Nat) then (1 : Nat) else 0) =
        if int256 x = 0 then (1 : Nat) else 0 from by
      rcases (int256_zero_iff_of_canonical hx) with ⟨h1, h2⟩
      split_ifs with ha hb hb
      · rfl
      · exact absurd (h2 ha) hb
      · exact absurd (h1 hb) ha
      · rfl]
  rw [evmIszero_ite, evmIszero_ite]
  rw [show (if int256 x < int256 mulExpRayHi then (0 : Nat) else 1) =
        if int256 mulExpRayHi ≤ int256 x then (1 : Nat) else 0 from by
      split_ifs <;> omega]
  rw [show (if int256 x = 0 then (0 : Nat) else 1) =
        if int256 x ≠ 0 then (1 : Nat) else 0 from by
      split_ifs <;> simp_all]
  rw [evmAnd_ite, evmAnd_ite, evmOr_ite, evmOr_ite]
  congr 1
  simp only [eq_iff_iff]
  constructor
  · rintro ((h | h) | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨h.1.1, h.1.2, h.2⟩)
  · rintro (h | h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨⟨h.1, h.2.1⟩, h.2.2⟩

/-- The guard word is zero exactly on the accepted inputs. -/
theorem mulExpGuardTree_eq_zero_iff {y x : Nat} (hx : x < 2 ^ 256) :
    mulExpGuardTree y x = 0 ↔
      absTree y ≤ scaleQ67 ∧ int256 x < int256 mulExpRayHi ∧
        (int256 x = 0 ∨ int256 x ≤ int256 mulExpRayZeroMax ∨
          2 ≤ int256 (mulShiftTree y x)) := by
  rw [mulExpGuardTree_eq_ite hx, ite_one_zero_eq_zero_iff]
  constructor
  · intro h
    push_neg at h
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨by omega, by omega, ?_⟩
    by_cases hx0 : int256 x = 0
    · exact Or.inl hx0
    · by_cases hzm : int256 x ≤ int256 mulExpRayZeroMax
      · exact Or.inr (Or.inl hzm)
      · exact Or.inr (Or.inr (by have := h3 hx0 (by omega); omega))
  · intro ⟨h1, h2, h3⟩
    push_neg
    refine ⟨by omega, by omega, ?_⟩
    intro hx0 hzm
    rcases h3 with h | h | h
    · exact absurd h hx0
    · omega
    · omega

/-- The guard word is one exactly on the rejected inputs. -/
theorem mulExpGuardTree_eq_one_iff {y x : Nat} (hx : x < 2 ^ 256) :
    mulExpGuardTree y x = 1 ↔
      scaleQ67 < absTree y ∨ int256 mulExpRayHi ≤ int256 x ∨
        (int256 x ≠ 0 ∧ int256 mulExpRayZeroMax < int256 x ∧
          int256 (mulShiftTree y x) < 2) := by
  rw [mulExpGuardTree_eq_ite hx, ite_one_zero_eq_one_iff]

/-- The value domain is exactly the guard word being zero. -/
theorem valueDomain_iff_guard_eq_zero {y x : Nat} (hcanon : MulExpRayCanonical y x) :
    MulExpRayValueDomain y x ↔ mulExpGuardTree y x = 0 := by
  rw [mulExpGuardTree_eq_zero_iff hcanon.2]
  unfold MulExpRayValueDomain
  exact ⟨fun h => h.2, fun h => ⟨hcanon, h⟩⟩

/-- The panic domain is exactly the guard word being one. -/
theorem panicDomain_iff_guard_eq_one {y x : Nat} (hcanon : MulExpRayCanonical y x) :
    MulExpRayPanicDomain y x ↔ mulExpGuardTree y x = 1 := by
  rw [mulExpGuardTree_eq_one_iff hcanon.2]
  unfold MulExpRayPanicDomain
  exact ⟨fun h => h.2, fun h => ⟨hcanon, h⟩⟩

end ExpYul

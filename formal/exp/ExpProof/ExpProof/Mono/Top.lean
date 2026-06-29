import ExpProof.Mono.Shell
import ExpProof.Mono.ShellOn
import ExpProof.Mono.RunBridge
import ExpProof.Mono.Pin

/-!
# Top-level monotonicity reduction

`expTree` is monotone over the supported domain once the analytic facts on the meaningful region
(`int256 C < int256 x`) are supplied:

* `r1Tree` is in range (`< 2^254`);
* `r1Tree` is nondecreasing in the signed input;
* the scale-point jump: `1 + r1Tree 0 ≤ r1Tree x` for any `x > 0` in the region (the `+1` pin at
  `x = 0` is bracketed by the exact-on-central neighbours).

The clamp forces `0` below the boundary, and `0 ≤ r1Tree` there above, so the boundary crossing is
order-preserving. Inputs are canonical words (`x < 2^256`, as the ABI decode produces). This file
bundles those facts as `RegionMonotonicityFacts` and derives `expTree_mono`.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

/-- The analytic monotonicity facts on the meaningful region `int256 C < int256 x < C0`
(for canonical words). -/
structure RegionMonotonicityFacts : Prop where
  /-- `r1Tree` never exceeds `≈ 2^123 < 2^254`. -/
  range : ∀ x : Nat, x < 2 ^ 256 → int256 Cmask < int256 x →
    int256 x < int256 C0thresh → r1Tree x < 2 ^ 254
  /-- `0 ≤ r1Tree` on the region (the floored `exp` value is never negative). -/
  nonneg : ∀ x : Nat, x < 2 ^ 256 → int256 Cmask < int256 x →
    int256 x < int256 C0thresh → 0 ≤ (r1Tree x : Int)
  /-- `r1Tree` is nondecreasing in the signed input across the region. -/
  mono : ∀ x1 x2 : Nat, x1 < 2 ^ 256 → x2 < 2 ^ 256 → int256 Cmask < int256 x1 →
    int256 x1 ≤ int256 x2 → int256 x2 < int256 C0thresh →
    (r1Tree x1 : Int) ≤ (r1Tree x2 : Int)
  /-- The scale-point jump: above `x = 0` the body has already cleared `1 + r1Tree 0`. -/
  pin : ∀ x : Nat, x < 2 ^ 256 → 0 < int256 x → int256 x < int256 C0thresh →
    1 + (r1Tree 0 : Int) ≤ (r1Tree x : Int)

theorem int256_C0thresh : int256 C0thresh = 44014845965556527147994239713 := by
  unfold C0thresh int256
  norm_num

/-- The region monotonicity facts hold given the octave-seam step: `range`/`nonneg` are
unconditional, and `mono`/`pin` reduce (via the same-octave step and the region induction) to
`SeamStep`. -/
theorem regionMonotonicityFacts_of_seam (hseamstep : SeamStep) : RegionMonotonicityFacts where
  range := fun x hx hC hC0 => r1Tree_range hx hC hC0
  nonneg := fun x _ _ _ => r1Tree_nonneg x
  mono := fun x1 x2 hx1 hx2 hC1 hle hC02 => by
    have h := r1Tree_region_mono hseamstep hx1 hx2 hC1 hle hC02
    -- transport `int256 ≤` to `Nat-cast ≤` (both below `2^254 < 2^255`)
    have hC2 : int256 Cmask < int256 x2 := lt_of_lt_of_le hC1 hle
    have hC01 : int256 x1 < int256 C0thresh := lt_of_le_of_lt hle hC02
    have hr1 : r1Tree x1 < 2 ^ 254 := r1Tree_range hx1 hC1 hC01
    have hr2 : r1Tree x2 < 2 ^ 254 := r1Tree_range hx2 hC2 hC02
    have e1 : int256 (r1Tree x1) = (r1Tree x1 : Int) :=
      int256_of_lt (by have : (2:Nat)^254 < 2^255 := by norm_num
                       omega)
    have e2 : int256 (r1Tree x2) = (r1Tree x2 : Int) :=
      int256_of_lt (by have : (2:Nat)^254 < 2^255 := by norm_num
                       omega)
    rw [e1, e2] at h; exact h
  pin := fun x hx hpos hC0 => r1Tree_pin hseamstep hx hpos hC0

theorem int256_Cmask_lt0 : int256 Cmask < 0 := by rw [int256_Cmask]; norm_num

theorem int256_zero : int256 (0 : Nat) = 0 := rfl

/-- For a canonical word, `int256 x = 0 ↔ x = 0`. -/
theorem int256_eq_zero_iff {x : Nat} (hx : x < 2 ^ 256) : int256 x = 0 ↔ x = 0 := by
  unfold int256
  simp only [intPow256] at *
  constructor
  · intro h; split at h <;> omega
  · intro h; subst h; rfl

theorem u256_id {x : Nat} (hx : x < 2 ^ 256) : u256 x = x := u256_of_lt hx

/-- **The tree monotonicity.** Under the region monotonicity facts, `int256 (expTree ·)` is
nondecreasing over the whole supported domain (`int256 x1 ≤ int256 x2 < C0`, canonical words). -/
theorem expTree_mono (H : RegionMonotonicityFacts) {x1 x2 : Nat}
    (hx1 : x1 < 2 ^ 256) (hx2 : x2 < 2 ^ 256)
    (hle : int256 x1 ≤ int256 x2)
    (hdom : int256 x2 < int256 C0thresh) :
    int256 (expTree x1) ≤ int256 (expTree x2) := by
  have hCneg : int256 Cmask < 0 := int256_Cmask_lt0
  have hu1 : u256 x1 = x1 := u256_id hx1
  have hu2 : u256 x2 = x2 := u256_id hx2
  have huC : u256 Cmask = Cmask := u256_id Cmask_lt
  -- Rewrite the boundary-comparison hypotheses into canonical form.
  by_cases h1 : int256 Cmask < int256 x1
  · -- x1 above the boundary ⇒ x2 above it too
    have h2 : int256 Cmask < int256 x2 := lt_of_lt_of_le h1 hle
    have hdom1 : int256 x1 < int256 C0thresh := lt_of_le_of_lt hle hdom
    have hr1 : r1Tree x1 < 2 ^ 254 := H.range x1 hx1 h1 hdom1
    have hr2 : r1Tree x2 < 2 ^ 254 := H.range x2 hx2 h2 hdom
    have hmask1 : int256 (u256 Cmask) < int256 (u256 x1) := by rw [huC, hu1]; exact h1
    have hmask2 : int256 (u256 Cmask) < int256 (u256 x2) := by rw [huC, hu2]; exact h2
    rw [int256_expTree_of_gt hmask1 hr1, int256_expTree_of_gt hmask2 hr2]
    have hmono : (r1Tree x1 : Int) ≤ (r1Tree x2 : Int) := H.mono x1 x2 hx1 hx2 h1 hle hdom
    rw [hu1, hu2]
    by_cases hz1 : x1 = 0
    · subst hz1
      have hzero : u256 (0 : Nat) = 0 := by rw [u256_zero]
      by_cases hz2 : x2 = 0
      · subst hz2; simp
      · -- x1 = 0 < x2
        have hx2pos : 0 < int256 x2 := by
          have hne : int256 x2 ≠ 0 := fun h => hz2 ((int256_eq_zero_iff hx2).mp h)
          have : (0 : Int) = int256 (0 : Nat) := int256_zero.symm
          omega
        have hpin := H.pin x2 hx2 hx2pos hdom
        rw [if_pos rfl, if_neg hz2]
        omega
    · by_cases hz2 : x2 = 0
      · subst hz2
        rw [if_neg hz1, if_pos rfl]
        omega
      · rw [if_neg hz1, if_neg hz2]; omega
  · -- x1 at/below the boundary ⇒ expTree x1 = 0
    have hx1le : int256 (u256 x1) ≤ int256 (u256 Cmask) := by rw [hu1, huC]; omega
    rw [expTree_eq_zero_of_le hx1le]
    by_cases h2 : int256 Cmask < int256 x2
    · have hr2 : r1Tree x2 < 2 ^ 254 := H.range x2 hx2 h2 hdom
      have hmask2 : int256 (u256 Cmask) < int256 (u256 x2) := by rw [huC, hu2]; exact h2
      rw [int256_expTree_of_gt hmask2 hr2]
      have hnn : 0 ≤ (r1Tree x2 : Int) := H.nonneg x2 hx2 h2 hdom
      have hz : int256 (0 : Nat) = 0 := int256_zero
      rw [hu2, hz]
      split <;> omega
    · have hx2le : int256 (u256 x2) ≤ int256 (u256 Cmask) := by rw [hu2, huC]; omega
      rw [expTree_eq_zero_of_le hx2le]

/-- A canonical word strictly below the supported threshold is in the non-reverting run domain. -/
theorem domain_of_below_C0 {x : Nat} (hx : x < 2 ^ 256) (h : int256 x < int256 C0thresh) :
    u256 x < 0x8e383a2cdfa1b74a9422d2e1 ∨ 2 ^ 255 ≤ u256 x := by
  rw [u256_id hx]
  rw [int256_C0thresh] at h
  by_cases hb : x < 2 ^ 255
  · left
    have : int256 x = (x : Int) := int256_of_lt hb
    rw [this] at h
    have : (x : Int) < 44014845965556527147994239713 := h
    have hC0 : (0x8e383a2cdfa1b74a9422d2e1 : Nat) = 44014845965556527147994239713 := by norm_num
    rw [hC0]; exact_mod_cast h
  · right; omega

/-- **Runtime monotonicity.** Under the region monotonicity facts, the compiled
`expRayToWad` signed results are `≤`-ordered for ordered canonical inputs strictly below the
supported threshold (the entire non-reverting `int256` domain). -/
theorem run_exp_ray_to_wad_evm_mono (H : RegionMonotonicityFacts) (x1 x2 : Nat)
    (hx1 : x1 < 2 ^ 256) (hx2 : x2 < 2 ^ 256)
    (hle : int256 x1 ≤ int256 x2) (hdom : int256 x2 < int256 C0thresh) :
    ∃ r1 r2, run_exp_ray_to_wad_evm x1 = .ok r1 ∧ run_exp_ray_to_wad_evm x2 = .ok r2 ∧
      int256 r1 ≤ int256 r2 := by
  have hdom1 : int256 x1 < int256 C0thresh := lt_of_le_of_lt hle hdom
  refine ⟨expTree x1, expTree x2, ?_, ?_, ?_⟩
  · exact run_exp_ray_to_wad_evm_eq_expTree x1 (domain_of_below_C0 hx1 hdom1)
  · exact run_exp_ray_to_wad_evm_eq_expTree x2 (domain_of_below_C0 hx2 hdom)
  · exact expTree_mono H hx1 hx2 hle hdom

/-- **Runtime monotonicity, modulo the octave seam.** With `range`/`nonneg` and the
same-octave/induction machinery all discharged, monotonicity over the entire non-reverting domain
follows from the single octave-seam step `SeamStep`. -/
theorem run_exp_ray_to_wad_evm_mono_of_seam (hseamstep : SeamStep) (x1 x2 : Nat)
    (hx1 : x1 < 2 ^ 256) (hx2 : x2 < 2 ^ 256)
    (hle : int256 x1 ≤ int256 x2) (hdom : int256 x2 < int256 C0thresh) :
    ∃ r1 r2, run_exp_ray_to_wad_evm x1 = .ok r1 ∧ run_exp_ray_to_wad_evm x2 = .ok r2 ∧
      int256 r1 ≤ int256 r2 :=
  run_exp_ray_to_wad_evm_mono (regionMonotonicityFacts_of_seam hseamstep) x1 x2 hx1 hx2 hle hdom

end ExpYul

import ExpProof.Floor.Spec
import ExpProof.Mono

/-!
# Public floor-bracket theorems for the compiled runtime

Assembling the floor brackets (`Floor.Spec`, given `RuntimeAccumBound`) and the clamp/pin shell
(`Mono.Shell`/`Mono.ShellOn`) into run-level statements about `run_exp_ray_to_wad_evm`.

The result word `expTree x` decomposes by the clamp boundary:

* `x = 0` — the scale point, `expTree 0 = 10¹⁸`; the brackets hold by the scale-point lemmas;
* `int256 x ≤ int256 Cmask` — below the 0/1 boundary, `expTree x = 0` and `E < 1`, so the global
  bracket holds with `r = 0`;
* the meaningful region with `x ≠ 0` — `int256 (expTree x) = int256 (r1Tree x)` (the clamp is
  transparent and the pin does not fire), so the `Floor.Spec` region brackets transport directly.

Each public theorem is stated on the runtime result `r` with `run_exp_ray_to_wad_evm x = .ok r`,
and carries the single analytic obligation `RuntimeAccumBound` (the cert-fold + truncation bridge),
exactly as `run_exp_ray_to_wad_evm_mono` carries `RegionMonotonicityFacts`.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation
open Common.Word
open ExpRealSpec

noncomputable section

set_option maxRecDepth 100000

/-! ## The result word equals the body on the region away from the scale point -/

/-- For a region input that is not the scale point, the run result is the body floor: above the
clamp boundary the clamp is transparent and the `x = 0` pin does not fire. -/
theorem int256_expTree_region_ne_zero {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) (hne : x ≠ 0) :
    int256 (expTree x) = int256 (r1Tree x) := by
  have hr1 : r1Tree x < 2 ^ 254 := r1Tree_range hx hC hC0
  have hmask : int256 (u256 Cmask) < int256 (u256 x) := by
    rw [u256_of_lt Cmask_lt, u256_of_lt hx]; exact hC
  rw [int256_expTree_of_gt hmask hr1]
  have hx0 : u256 x ≠ 0 := by rw [u256_of_lt hx]; exact hne
  have hr1eq : int256 (r1Tree x) = (r1Tree x : Int) :=
    int256_of_lt (by have : (2:Nat)^254 < 2^255 := by norm_num
                     omega)
  rw [if_neg hx0, zero_add, hr1eq]

/-! ## Global never-over and floor-or-one-less bracket -/

/-- **Global floor-or-one-less bracket.** Given the analytic accumulator bound, for every signed input strictly
below the supported threshold the runtime result `r` satisfies the 2-wide never-over bracket
`r ≤ E ∧ E < r + 2`. -/
theorem run_exp_ray_to_wad_evm_floorOrOneLess (H' : RuntimeAccumBound) (x : Nat) (hx : x < 2 ^ 256)
    (hC0 : int256 x < int256 C0thresh) :
    ∃ r, run_exp_ray_to_wad_evm x = .ok r ∧ FloorOrOneLessBracket (int256 x) (int256 r) := by
  refine ⟨expTree x, run_exp_ray_to_wad_evm_eq_expTree x (domain_of_below_C0 hx hC0), ?_⟩
  by_cases hC : int256 Cmask < int256 x
  · by_cases hz : x = 0
    · -- scale point
      subst hz
      have he : expTree 0 = 1000000000000000000 := by
        have := run_exp_ray_to_wad_evm_zero
        rw [run_exp_ray_to_wad_evm_eq_expTree 0 (domain_of_below_C0 hx hC0)] at this
        exact Except.ok.inj this.symm
      rw [he]
      have h0 : int256 (1000000000000000000 : Nat) = (10 ^ 18 : Int) := by
        rw [int256_of_lt (by norm_num)]; norm_num
      have hi0 : int256 (0 : Nat) = (0 : Int) := rfl
      rw [h0, hi0]; exact floorOrOneLess_zero
    · rw [int256_expTree_region_ne_zero hx hC hC0 hz]
      exact floorOrOneLessBracket_region H' hx hC hC0
  · -- below/at the clamp boundary: result is 0, E < 1
    push_neg at hC
    have hle : int256 (u256 x) ≤ int256 (u256 Cmask) := by
      rw [u256_of_lt hx, u256_of_lt Cmask_lt]; exact hC
    have hle' : int256 x ≤ int256 Cmask := by
      rw [u256_of_lt hx, u256_of_lt Cmask_lt] at hle; exact hle
    rw [expTree_eq_zero_of_le hle]
    have hz0 : int256 (0 : Nat) = 0 := rfl
    rw [hz0]
    refine ⟨?_, ?_⟩
    · rw [Int.cast_zero]
      have hpos : (0 : Real) ≤ expRayToWadTarget (int256 x) := by
        unfold expRayToWadTarget
        have := Real.exp_pos ((int256 x : Real) / (RAY : Real))
        positivity
      exact hpos
    · have := H'.belowC x hle'
      rw [Int.cast_zero]; linarith [this]

/-! ## One-unit underestimation bound -/

/-- **One-unit underestimation bound (global).** Given the analytic accumulator bound, the runtime result
underestimates by at most one output unit: `⌊E⌋ − 1 ≤ r`. -/
theorem run_exp_ray_to_wad_evm_underByAtMostOne (H' : RuntimeAccumBound) (x : Nat) (hx : x < 2 ^ 256)
    (hC0 : int256 x < int256 C0thresh) :
    ∃ r, run_exp_ray_to_wad_evm x = .ok r ∧ UnderByAtMostOne (int256 x) (int256 r) := by
  obtain ⟨r, hrun, hbr⟩ := run_exp_ray_to_wad_evm_floorOrOneLess H' x hx hC0
  exact ⟨r, hrun, floorOrOneLess_to_underByAtMostOne hbr⟩

end

end ExpYul

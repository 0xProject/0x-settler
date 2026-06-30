import ExpProof.Floor.Public
import ExpProof.Floor.R0BoundHolds

/-!
# Hypothesis-free global floor brackets for the compiled runtime

The global floor-or-one-less and one-unit underestimation brackets consume only the
never-over/deficit/below-clamp facts (`accumReal_over`, `accumReal_under`,
`belowC_target_lt_one`). They become hypothesis-free here.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation
open Common.Word
open ExpRealSpec

noncomputable section

set_option maxRecDepth 100000

/-- **Global floor-or-one-less bracket.** For every signed input strictly below the supported
threshold the runtime result `r` satisfies the 2-wide never-over bracket `r ≤ E ∧ E < r + 2`. -/
theorem run_exp_ray_to_wad_evm_floorOrOneLess_uncond (x : Nat) (hx : x < 2 ^ 256)
    (hC0 : int256 x < int256 C0thresh) :
    ∃ r, run_exp_ray_to_wad_evm x = .ok r ∧ FloorOrOneLessBracket (int256 x) (int256 r) := by
  refine ⟨expTree x, run_exp_ray_to_wad_evm_eq_expTree x (domain_of_below_C0 hx hC0), ?_⟩
  by_cases hC : int256 Cmask < int256 x
  · by_cases hz : x = 0
    · subst hz
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
      exact floorOrOneLessBracket_region_uncond hx hC hC0
  · push_neg at hC
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
    · have := belowC_target_lt_one hle'
      rw [Int.cast_zero]; linarith [this]

/-- **One-unit underestimation bound (global).** `⌊E⌋ − 1 ≤ r`. -/
theorem run_exp_ray_to_wad_evm_underByAtMostOne_uncond (x : Nat) (hx : x < 2 ^ 256)
    (hC0 : int256 x < int256 C0thresh) :
    ∃ r, run_exp_ray_to_wad_evm x = .ok r ∧ UnderByAtMostOne (int256 x) (int256 r) := by
  obtain ⟨r, hrun, hbr⟩ := run_exp_ray_to_wad_evm_floorOrOneLess_uncond x hx hC0
  exact ⟨r, hrun, floorOrOneLess_to_underByAtMostOne hbr⟩

end

end ExpYul

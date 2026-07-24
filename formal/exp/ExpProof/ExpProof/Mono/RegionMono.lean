import ExpProof.Mono.StepMono

/-!
# Lifting the adjacent step to the whole region

The octave index advances by at most one per unit input step (`kTree_step`). Combined with the
same-octave step (`r1_mono_adjacent`) and the octave-seam step, the unit step `r1Tree x1 ≤
r1Tree x2` (for `int256 x2 = int256 x1 + 1` in region) holds; induction over the signed-integer
interval then gives `r1Tree` nondecreasing across the whole region.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

/-- The octave index advances by `0` or `1` per unit input step (`CINV ≪ 2^192`). -/
theorem kTree_step_wide {x1 x2 : Nat} (hx1 : x1 < 2 ^ 256) (hx2 : x2 < 2 ^ 256)
    (hW1 : WideRegion x1) (hW2 : WideRegion x2)
    (hadj : int256 x2 = int256 x1 + 1) :
    int256 (kTree x2) = int256 (kTree x1) ∨ int256 (kTree x2) = int256 (kTree x1) + 1 := by
  obtain ⟨hlo1, hhi1⟩ := kTree_sandwich_wide hx1 hW1
  obtain ⟨hlo2, hhi2⟩ := kTree_sandwich_wide hx2 hW2
  have hmono := kTree_mono_wide hx1 hx2 hW1.1 (by omega) hW2.2
  -- the rounding argument advances by exactly `CINV < 2^192`
  set k1 := int256 (kTree x1)
  set k2 := int256 (kTree x2)
  have hcinv : (0x724d54edbacbebbb95c52a0f60 : Int) < 2 ^ 192 := by norm_num
  have hcinvpos : (0 : Int) < 0x724d54edbacbebbb95c52a0f60 := by norm_num
  have hp200 : (0 : Int) < 2 ^ 192 := by norm_num
  -- argument at x2 exceeds that at x1 by exactly CINV
  have hstep : (2 ^ 191 : Int) + 0x724d54edbacbebbb95c52a0f60 * int256 x2 =
      (2 ^ 191 + 0x724d54edbacbebbb95c52a0f60 * int256 x1) + 0x724d54edbacbebbb95c52a0f60 := by
    rw [hadj]; ring
  rw [hstep] at hlo2 hhi2
  -- 2^192·k2 ≤ A + CINV < 2^192·k1 + 2^192 + CINV < 2^192·(k1 + 2), so k2 < k1 + 2 ⇒ k2 ≤ k1 + 1
  have hupper : k2 < k1 + 2 := by nlinarith [hlo2, hhi1, hcinv, hp200]
  omega

theorem kTree_step {x1 x2 : Nat} (hx1 : x1 < 2 ^ 256) (hx2 : x2 < 2 ^ 256)
    (hC1 : int256 Cmask < int256 x1) (hC01 : int256 x1 < int256 C0thresh)
    (hC2 : int256 Cmask < int256 x2) (hC02 : int256 x2 < int256 C0thresh)
    (hadj : int256 x2 = int256 x1 + 1) :
    int256 (kTree x2) = int256 (kTree x1) ∨ int256 (kTree x2) = int256 (kTree x1) + 1 :=
  kTree_step_wide hx1 hx2 (wideRegion_of_wad hC1 hC01) (wideRegion_of_wad hC2 hC02) hadj

/-- **The octave-seam step** (`k` advances by one): `r1Tree` is nondecreasing across the boundary.
The accumulators are still nearly constant (`v_a ≈ v_b`), the reduced argument flips sign
(`t_b ≈ −t_a`), and the closing shift loses one bit, so `r1Tree x1 ≤ r1Tree x2`. Carried as an
explicit hypothesis (`SeamStep`) until its analytic certificate is discharged; the same-octave step
and the induction below are unconditional. -/
def SeamStep : Prop :=
  ∀ {x1 x2 : Nat}, x1 < 2 ^ 256 → x2 < 2 ^ 256 →
    int256 Cmask < int256 x1 → int256 x1 < int256 C0thresh →
    int256 Cmask < int256 x2 → int256 x2 < int256 C0thresh →
    int256 (kTree x2) = int256 (kTree x1) + 1 →
    int256 x2 = int256 x1 + 1 →
    int256 (r1Tree x1) ≤ int256 (r1Tree x2)

/-- **The unit step**: `r1Tree` is nondecreasing for two inputs adjacent in the signed order
(same-octave proved; the seam supplied by `SeamStep`). -/
theorem r1_step (hseamstep : SeamStep) {x1 x2 : Nat} (hx1 : x1 < 2 ^ 256) (hx2 : x2 < 2 ^ 256)
    (hC1 : int256 Cmask < int256 x1) (hC01 : int256 x1 < int256 C0thresh)
    (hC2 : int256 Cmask < int256 x2) (hC02 : int256 x2 < int256 C0thresh)
    (hadj : int256 x2 = int256 x1 + 1) :
    int256 (r1Tree x1) ≤ int256 (r1Tree x2) := by
  rcases kTree_step hx1 hx2 hC1 hC01 hC2 hC02 hadj with hsame | hseam
  · exact r1_mono_adjacent hx1 hx2 hC1 hC01 hC2 hC02 hsame.symm hadj
  · exact hseamstep hx1 hx2 hC1 hC01 hC2 hC02 hseam hadj

/-! ## The integer-step induction -/

/-- A signed value strictly inside the region is a canonical word with that signed value. -/
theorem region_word {v : Int} (hlo : int256 Cmask < v) (hhi : v < int256 C0thresh) :
    uint256OfInt v < 2 ^ 256 ∧ int256 (uint256OfInt v) = v := by
  have hC0 : int256 C0thresh = 45401140326676417766828703956 := int256_C0thresh
  have hCm : int256 Cmask = -41446531673892822312323846185 := int256_Cmask
  rw [hCm] at hlo; rw [hC0] at hhi
  refine ⟨uint256OfInt_lt v, ?_⟩
  refine int256_uint256OfInt ?_ ?_
  · simp only [ipow255]; omega
  · simp only [ipow255]; omega

/-- Induction on the number of unit steps: `r1Tree` is nondecreasing from any region input to one
`n` steps above it (every intermediate value staying in the region). -/
theorem r1_mono_steps (hseamstep : SeamStep) (n : Nat) : ∀ x1 : Nat, x1 < 2 ^ 256 →
    int256 Cmask < int256 x1 → int256 x1 + n < int256 C0thresh →
    int256 (r1Tree x1) ≤ int256 (r1Tree (uint256OfInt (int256 x1 + n))) := by
  induction n with
  | zero =>
    intro x1 hx1 hC1 _
    have hw : uint256OfInt (int256 x1 + (0 : Nat)) = x1 := by
      rw [show ((0 : Nat) : Int) = 0 by rfl, Int.add_zero]
      exact uint256OfInt_int256 hx1
    rw [hw]
  | succ m ih =>
    intro x1 hx1 hC1 hbnd
    -- the step target `x1 + 1`
    obtain ⟨hw1lt, hw1eq⟩ := region_word (v := int256 x1 + 1) (by omega) (by
      have : int256 x1 + (m + 1 : Nat) < int256 C0thresh := hbnd
      push_cast at this; omega)
    set y := uint256OfInt (int256 x1 + 1) with hy
    have hCy : int256 Cmask < int256 y := by rw [hw1eq]; omega
    have hCy0 : int256 y < int256 C0thresh := by
      rw [hw1eq]
      have : int256 x1 + (m + 1 : Nat) < int256 C0thresh := hbnd
      push_cast at this; omega
    -- the unit step x1 → y
    have hstep : int256 (r1Tree x1) ≤ int256 (r1Tree y) :=
      r1_step hseamstep hx1 hw1lt hC1 (by omega) hCy hCy0 (by rw [hw1eq])
    -- m steps from y
    have hrec := ih y hw1lt hCy (by
      rw [hw1eq]
      have : int256 x1 + (m + 1 : Nat) < int256 C0thresh := hbnd
      push_cast at this; omega)
    -- `int256 y + m = int256 x1 + (m + 1)`
    have hsum : int256 y + (m : Int) = int256 x1 + (m + 1 : Nat) := by rw [hw1eq]; push_cast; ring
    rw [hsum] at hrec
    have htgt : int256 x1 + ((m : Nat) + 1 : Nat) = int256 x1 + (m + 1 : Nat) := by push_cast; ring
    calc int256 (r1Tree x1) ≤ int256 (r1Tree y) := hstep
      _ ≤ int256 (r1Tree (uint256OfInt (int256 x1 + (m + 1 : Nat)))) := hrec

/-- **Region monotonicity of `r1Tree`** (the `RegionMonotonicityFacts.mono` field): for canonical inputs in
the region with `int256 x1 ≤ int256 x2`, `r1Tree x1 ≤ r1Tree x2`. -/
theorem r1Tree_region_mono (hseamstep : SeamStep) {x1 x2 : Nat}
    (hx1 : x1 < 2 ^ 256) (hx2 : x2 < 2 ^ 256)
    (hC1 : int256 Cmask < int256 x1) (hle : int256 x1 ≤ int256 x2)
    (hC02 : int256 x2 < int256 C0thresh) :
    int256 (r1Tree x1) ≤ int256 (r1Tree x2) := by
  -- `x2 = uint256OfInt (int256 x1 + n)` with `n = (int256 x2 − int256 x1).toNat`
  set n := (int256 x2 - int256 x1).toNat with hn
  have hnval : (n : Int) = int256 x2 - int256 x1 := by
    rw [hn]; exact Int.toNat_of_nonneg (by omega)
  have hbnd : int256 x1 + (n : Int) < int256 C0thresh := by rw [hnval]; omega
  have hstep := r1_mono_steps hseamstep n x1 hx1 hC1 hbnd
  -- `uint256OfInt (int256 x1 + n) = x2`
  have hx2eq : int256 x1 + (n : Int) = int256 x2 := by rw [hnval]; ring
  have hcanon : uint256OfInt (int256 x1 + (n : Int)) = x2 := by
    rw [hx2eq]; exact uint256OfInt_int256 hx2
  rw [hcanon] at hstep
  exact hstep

end ExpYul

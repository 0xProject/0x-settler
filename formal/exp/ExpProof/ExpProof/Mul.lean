import ExpProof.Mono.MulTree
import ExpProof.ExpYulRuntime
import ExpProof.Spec.RealExp

/-!
# `mulExpRay` proof facade

This module states the public runtime specifications for `mulExpRay` and exposes the proof
obligations that connect the compiled run to the arithmetic tree. The tree is defined in
`Mono.MulTree`; consumers supply proofs that the tree satisfies the real bracket and monotonicity
predicates below.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation
open ExpRealSpec

noncomputable section

/-- The public bracket spec for one successful `mulExpRay` run. -/
def MulExpRayRunBracket (y x : Nat) : Prop :=
  ∃ r, run_mul_exp_ray_evm y x = .ok r ∧
    MulExpRayBracket (int256 y) (int256 x) (int256 r)

/-- The public monotonicity spec for two successful `mulExpRay` runs at a fixed multiplier. -/
def MulExpRayRunMonotone (y x1 x2 : Nat) : Prop :=
  ∃ r1 r2, run_mul_exp_ray_evm y x1 = .ok r1 ∧ run_mul_exp_ray_evm y x2 = .ok r2 ∧
    MulExpRaySignedMonotone (int256 y) (int256 x1) (int256 x2) (int256 r1) (int256 r2)

/-- Runtime bracket proof obligation for the named arithmetic tree. -/
theorem mulExpRay_run_bracket_of_tree
    {y x : Nat}
    (hrun : run_mul_exp_ray_evm y x = .ok (mulExpTree y x))
    (hbracket : MulExpRayBracket (int256 y) (int256 x) (int256 (mulExpTree y x))) :
    MulExpRayRunBracket y x :=
  ⟨mulExpTree y x, hrun, hbracket⟩

/-- Runtime monotonicity proof obligation for the named arithmetic tree. -/
theorem mulExpRay_run_monotone_of_tree
    {y x1 x2 : Nat}
    (hrun1 : run_mul_exp_ray_evm y x1 = .ok (mulExpTree y x1))
    (hrun2 : run_mul_exp_ray_evm y x2 = .ok (mulExpTree y x2))
    (hmono : MulExpRaySignedMonotone (int256 y) (int256 x1) (int256 x2)
      (int256 (mulExpTree y x1)) (int256 (mulExpTree y x2))) :
    MulExpRayRunMonotone y x1 x2 :=
  ⟨mulExpTree y x1, mulExpTree y x2, hrun1, hrun2, hmono⟩

/-- The zero-magnitude result satisfies the signed `mulExpRay` bracket for every exponent. -/
theorem mulExpRayBracket_zero_result (x : Int) :
    MulExpRayBracket 0 x 0 := by
  simp [MulExpRayBracket, mulExpRayMagnitudeBracket_zero]

/-- A proved zero-magnitude runtime result immediately satisfies the public bracket spec. -/
theorem mulExpRay_run_bracket_zero_of_run {x : Nat}
    (hrun : run_mul_exp_ray_evm 0 x = .ok 0) :
    MulExpRayRunBracket 0 x :=
  ⟨0, hrun, mulExpRayBracket_zero_result (int256 x)⟩

/-- The `y = 10^18` magnitude target is the existing `expRayToWad` target. -/
theorem mulExpRayMagnitudeTarget_wad (x : Int) :
    mulExpRayMagnitudeTarget (10 ^ 18) x = expRayToWadTarget x := by
  simp [mulExpRayMagnitudeTarget, expRayToWadTarget, WAD]

/-- Existing `expRayToWad` floor brackets instantiate the `mulExpRay` bracket at `y = 10^18`. -/
theorem floorOrOneLess_to_mulExpRayBracket_wad {x r : Int}
    (hr : 0 ≤ r) (h : FloorOrOneLessBracket x r) :
    MulExpRayBracket (10 ^ 18) x r := by
  rw [MulExpRayBracket]
  norm_num
  have hw := mulExpRayMagnitudeTarget_wad x
  norm_num at hw
  exact ⟨hr, by simpa [hw] using h.1, by simpa [hw] using h.2⟩

/-- Runtime specialization proof obligation for the existing `expRayToWad` theorem stack. -/
theorem mulExpRay_run_bracket_wad_of_exp
    {x r : Nat}
    (hrun : run_mul_exp_ray_evm (10 ^ 18) x = .ok r)
    (hr : 0 ≤ int256 r)
    (hexp : FloorOrOneLessBracket (int256 x) (int256 r)) :
    MulExpRayRunBracket (10 ^ 18) x :=
  ⟨r, hrun, floorOrOneLess_to_mulExpRayBracket_wad hr hexp⟩

end

end ExpYul

import ExpProof.Mono.MulTree
import ExpProof.ExpYulRuntime
import ExpProof.Spec.RealExp
import ExpProof.Seam.MulValue
import ExpProof.Seam.MulRevert
import ExpProof.Mul.Domain
import ExpProof.Mul.Bridge

/-!
# `mulExpRay` public runtime specifications

This module states the public runtime specifications for `mulExpRay` — the signed bracket and
the three monotonicity forms over successful runs — together with the shell results that need no
polynomial certificate. The tree is defined in `Mono.MulTree`; the bracket and monotonicity
statements are discharged in `Mul.Accum`, `Mul.XMono`, `Mul.YMono`, and `Mul.Joint`.
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

/-- The public monotonicity-in-`x` spec for two successful runs at a fixed multiplier. -/
def MulExpRayRunMonotone (y x1 x2 : Nat) : Prop :=
  ∃ r1 r2, run_mul_exp_ray_evm y x1 = .ok r1 ∧ run_mul_exp_ray_evm y x2 = .ok r2 ∧
    MulExpRaySignedMonotone (int256 y) (int256 x1) (int256 x2) (int256 r1) (int256 r2)

/-- The public monotonicity-in-`y` spec for two successful runs at a fixed exponent. -/
def MulExpRayRunYMonotone (y1 y2 x : Nat) : Prop :=
  ∃ r1 r2, run_mul_exp_ray_evm y1 x = .ok r1 ∧ run_mul_exp_ray_evm y2 x = .ok r2 ∧
    MulExpRayYMonotone (int256 y1) (int256 y2) (int256 x) (int256 r1) (int256 r2)

/-- The public sign-aware joint monotonicity spec for two successful runs. -/
def MulExpRayRunJointMonotone (y1 y2 x1 x2 : Nat) : Prop :=
  ∃ r1 r2, run_mul_exp_ray_evm y1 x1 = .ok r1 ∧ run_mul_exp_ray_evm y2 x2 = .ok r2 ∧
    MulExpRayJointMonotone (int256 y1) (int256 y2) (int256 x1) (int256 x2)
      (int256 r1) (int256 r2)

/-- The zero-magnitude result satisfies the signed `mulExpRay` bracket for every exponent. -/
theorem mulExpRayBracket_zero_result (x : Int) :
    MulExpRayBracket 0 x 0 := by
  simp [MulExpRayBracket, mulExpRayMagnitudeBracket_zero]

/-- A proved zero-magnitude runtime result immediately satisfies the public bracket spec. -/
theorem mulExpRay_run_bracket_zero_of_run {x : Nat}
    (hrun : run_mul_exp_ray_evm 0 x = .ok 0) :
    MulExpRayRunBracket 0 x :=
  ⟨0, hrun, mulExpRayBracket_zero_result (int256 x)⟩

/-- The compiled runtime returns zero for a zero multiplier whenever the guard accepts:
`sgn(0) = 0` collapses the kernel output at the tree level. -/
theorem run_mul_exp_ray_evm_zero_of_guard (x : Nat)
    (hguard : mulExpGuardTree 0 x = 0) :
    run_mul_exp_ray_evm 0 x = .ok 0 := by
  simpa [mulExpTree_zero] using run_mul_exp_ray_evm_eq_tree_of_guard 0 x hguard

/-- The compiled runtime satisfies the public bracket spec at zero magnitude whenever the guard
accepts. -/
theorem mulExpRay_run_bracket_zero (x : Nat) (hguard : mulExpGuardTree 0 x = 0) :
    MulExpRayRunBracket 0 x :=
  mulExpRay_run_bracket_zero_of_run (run_mul_exp_ray_evm_zero_of_guard x hguard)

/-- **Value path on the domain.** Accepted inputs return the compiled arithmetic tree. -/
theorem run_mul_exp_ray_evm_eq_tree {y x : Nat} (h : MulExpRayValueDomain y x) :
    run_mul_exp_ray_evm y x = .ok (mulExpTree y x) :=
  run_mul_exp_ray_evm_eq_tree_of_guard y x ((valueDomain_iff_guard_eq_zero h.1).mp h)

/-- **Panic revert.** Rejected inputs revert. -/
theorem run_mul_exp_ray_evm_revert {y x : Nat} (h : MulExpRayPanicDomain y x) :
    run_mul_exp_ray_evm y x = .error "revert" :=
  run_mul_exp_ray_evm_revert_of_guard y x ((panicDomain_iff_guard_eq_one h.1).mp h)

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

/-- Runtime specialization: an `expRayToWad` floor bracket instantiates the `mulExpRay`
bracket at `y = 10¹⁸`. -/
theorem mulExpRay_run_bracket_wad_of_exp
    {x r : Nat}
    (hrun : run_mul_exp_ray_evm (10 ^ 18) x = .ok r)
    (hr : 0 ≤ int256 r)
    (hexp : FloorOrOneLessBracket (int256 x) (int256 r)) :
    MulExpRayRunBracket (10 ^ 18) x :=
  ⟨r, hrun, floorOrOneLess_to_mulExpRayBracket_wad hr hexp⟩

end

end ExpYul

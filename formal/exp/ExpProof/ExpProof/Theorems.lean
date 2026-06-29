import ExpProof.Seam.Revert
import ExpProof.Seam.Value
import ExpProof.Mono

/-!
# `expRayToWad` — proven properties of the compiled runtime (signpost)

This file is the at-a-glance demonstration that the documented properties hold for *the
interpretation of the implementation*: the EVMYulLean execution of the compiled `ExpWrapper` Yul,
`run_exp_ray_to_wad_evm` (defined in the generated `ExpYulRuntime`). Each property below is a
runtime-level theorem; the axiom gate at the bottom pins it to Lean's three standard axioms, so a
stray `sorry` (or any new axiom) breaks the build.

## Documented properties (about the runtime)

| Property                                        | Theorem                          |
|-------------------------------------------------|----------------------------------|
| Reverts on inputs ≥ `0x8e383a2cdfa1b74a9422d2e1`| `run_exp_ray_to_wad_evm_revert`  |
| Scale point: `expRayToWad(0) = 10^18`           | `run_exp_ray_to_wad_evm_zero`    |
| Value path reduces to the `evm*` tree           | `run_exp_ray_to_wad_evm_eq_tree` |
| Monotone in the input (modulo the region core)  | `run_exp_ray_to_wad_evm_mono`    |

The monotonicity theorem `run_exp_ray_to_wad_evm_mono` is proved over the whole supported domain;
it takes the analytic facts of the meaningful region (`RegionMonotonicityFacts`: `r1Tree` in range,
nonnegative, nondecreasing, and the scale-point pin clearance) as a hypothesis. The clamp/pin
shell, the run-level bridge, and the octave-index / reduced-argument transports and their
monotonicity are proved without that hypothesis; the rational-quotient (`sdiv`) within-octave step
and the octave-seam compensation are represented by `RegionMonotonicityFacts`.

The supported-range threshold is `0x8e383a2cdfa1b74a9422d2e1`; at or above it (and below `2^255`,
i.e. for any non-negative `int256` that large) the wrapper run halts with `revert`. At the scale
point `x = 0` the run returns the wad unit `10^18` exactly. For any signed input strictly below the
threshold the run returns the inline `evm*` arithmetic tree (the handle for the floor/monotone/bound
properties), reduced with no hand model.
-/

namespace ExpYul

open FormalYul

/-- Reverts above the supported range. -/
example (x : Nat)
    (h1 : (0x8e383a2cdfa1b74a9422d2e1 : Nat) ≤ FormalYul.u256 x)
    (h2 : FormalYul.u256 x < 2 ^ 255) :
    run_exp_ray_to_wad_evm x = .error "revert" :=
  run_exp_ray_to_wad_evm_revert x h1 h2

/-- `expRayToWad(0)` returns the wad unit exactly. -/
example : run_exp_ray_to_wad_evm 0 = .ok 1000000000000000000 :=
  run_exp_ray_to_wad_evm_zero

/-- info: 'ExpYul.run_exp_ray_to_wad_evm_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_exp_ray_to_wad_evm_revert

/-- info: 'ExpYul.run_exp_ray_to_wad_evm_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_exp_ray_to_wad_evm_zero

/-- info: 'ExpYul.run_exp_ray_to_wad_evm_eq_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_exp_ray_to_wad_evm_eq_tree

/-- Monotone over the whole supported domain, given the meaningful-region analytic core. -/
example (H : RegionMonotonicityFacts) (x1 x2 : Nat)
    (hx1 : x1 < 2 ^ 256) (hx2 : x2 < 2 ^ 256)
    (hle : FormalYul.Preservation.int256 x1 ≤ FormalYul.Preservation.int256 x2)
    (hdom : FormalYul.Preservation.int256 x2 < FormalYul.Preservation.int256 C0thresh) :
    ∃ r1 r2, run_exp_ray_to_wad_evm x1 = .ok r1 ∧ run_exp_ray_to_wad_evm x2 = .ok r2 ∧
      FormalYul.Preservation.int256 r1 ≤ FormalYul.Preservation.int256 r2 :=
  run_exp_ray_to_wad_evm_mono H x1 x2 hx1 hx2 hle hdom

/-- info: 'ExpYul.run_exp_ray_to_wad_evm_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_exp_ray_to_wad_evm_mono

/-- Monotone over the whole supported domain, reduced to the single analytic obligation
`SeamR0Bound` (the octave-seam `r0` doubling bound). The kernel-wall floor reduction, the
`range`/`nonneg` obligations, the same-octave step, the region induction, and the scale-point pin are
all proved unconditionally; what remains for an unconditional monotonicity theorem is the minimax
accuracy bound `SeamR0Bound`. -/
example (hr0 : SeamR0Bound) (x1 x2 : Nat)
    (hx1 : x1 < 2 ^ 256) (hx2 : x2 < 2 ^ 256)
    (hle : FormalYul.Preservation.int256 x1 ≤ FormalYul.Preservation.int256 x2)
    (hdom : FormalYul.Preservation.int256 x2 < FormalYul.Preservation.int256 C0thresh) :
    ∃ r1 r2, run_exp_ray_to_wad_evm x1 = .ok r1 ∧ run_exp_ray_to_wad_evm x2 = .ok r2 ∧
      FormalYul.Preservation.int256 r1 ≤ FormalYul.Preservation.int256 r2 :=
  run_exp_ray_to_wad_evm_mono_of_seamR0 hr0 x1 x2 hx1 hx2 hle hdom

/-- info: 'ExpYul.run_exp_ray_to_wad_evm_mono_of_seamR0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_exp_ray_to_wad_evm_mono_of_seamR0

end ExpYul

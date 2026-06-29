import ExpProof.Seam.Revert

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

The supported-range threshold is `0x8e383a2cdfa1b74a9422d2e1`; at or above it (and below `2^255`,
i.e. for any non-negative `int256` that large) the wrapper run halts with `revert`.
-/

namespace ExpYul

open FormalYul

/-- Reverts above the supported range. -/
example (x : Nat)
    (h1 : (0x8e383a2cdfa1b74a9422d2e1 : Nat) ≤ FormalYul.u256 x)
    (h2 : FormalYul.u256 x < 2 ^ 255) :
    run_exp_ray_to_wad_evm x = .error "revert" :=
  run_exp_ray_to_wad_evm_revert x h1 h2

/-- info: 'ExpYul.run_exp_ray_to_wad_evm_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_exp_ray_to_wad_evm_revert

end ExpYul

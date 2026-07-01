import ExpProof.Seam.Revert
import ExpProof.Seam.Value
import ExpProof.Mono
import ExpProof.Mono.SeamR0
import ExpProof.Floor.PublicUncond
import ExpProof.Floor.R0BoundHolds
import ExpProof.Floor.R0Bound
import ExpProof.Floor.RoundTrip

/-!
# `expRayToWad` — proven properties of the compiled runtime (signpost)

This file is the at-a-glance demonstration that the documented properties hold for *the
interpretation of the implementation*: the EVMYulLean execution of the compiled `ExpWrapper` Yul,
`run_exp_ray_to_wad_evm` (defined in the generated `ExpYulRuntime`). Each property below is a
runtime-level theorem; the axiom gate at the bottom pins it to Lean's three standard axioms, so a
stray `sorry` (or any new axiom) breaks the build.

## Documented properties (about the runtime)

| Property                                          | Theorem                                          |
|---------------------------------------------------|--------------------------------------------------|
| Reverts on inputs ≥ `0x8e383a2cdfa1b74a9422d2e1`  | `run_exp_ray_to_wad_evm_revert`                  |
| Scale point: `expRayToWad(0) = 10^18`             | `run_exp_ray_to_wad_evm_zero`                    |
| Value path reduces to the `evm*` tree             | `run_exp_ray_to_wad_evm_eq_tree`                 |
| Never over / floor-or-one-less: `r ≤ E < r + 2`   | `run_exp_ray_to_wad_evm_floorOrOneLess_uncond`   |
| Underestimates by at most one: `⌊E⌋ − 1 ≤ r`      | `run_exp_ray_to_wad_evm_underByAtMostOne_uncond` |
| Monotone in the input                             | `run_exp_ray_to_wad_evm_mono_unconditional`      |
| `lnWadToRay` round trip                           | `run_exp_ray_to_wad_evm_lnWadToRay_roundTrip_if` |

Every property is unconditional. The monotonicity analytic core (`RegionMonotonicityFacts`,
reduced to the octave-seam `r0` doubling bound `SeamR0Bound`) is discharged by
`seamR0Bound_holds`; the floor brackets consume the discharged accumulator facts
(`accumReal_over`, `accumReal_under`, `belowC_target_lt_one`) directly.

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

/-! ## Monotonicity

The octave-seam `r0`-doubling bound `SeamR0Bound` is discharged (`seamR0Bound_holds`, via the
per-point real bracket `r0Tree x ≈ 2¹²⁶·exp(rt)` and the seam relation `exp(rt1) =
2·exp(rt2)·exp(−1/RAY)`), so monotonicity holds over the whole supported domain with no analytic
hypothesis. -/

/-- Monotone over the whole supported domain. -/
example (x1 x2 : Nat)
    (hx1 : x1 < 2 ^ 256) (hx2 : x2 < 2 ^ 256)
    (hle : FormalYul.Preservation.int256 x1 ≤ FormalYul.Preservation.int256 x2)
    (hdom : FormalYul.Preservation.int256 x2 < FormalYul.Preservation.int256 C0thresh) :
    ∃ r1 r2, run_exp_ray_to_wad_evm x1 = .ok r1 ∧ run_exp_ray_to_wad_evm x2 = .ok r2 ∧
      FormalYul.Preservation.int256 r1 ≤ FormalYul.Preservation.int256 r2 :=
  run_exp_ray_to_wad_evm_mono_unconditional x1 x2 hx1 hx2 hle hdom

/-- info: 'ExpYul.run_exp_ray_to_wad_evm_mono_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_exp_ray_to_wad_evm_mono_unconditional

/-- info: 'ExpYul.seamR0Bound_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms seamR0Bound_holds

/-! ## `Real.exp` floor brackets

Each bracket is stated on the runtime result `r` (`run_exp_ray_to_wad_evm x = .ok r`) against the
target `E = 10¹⁸·exp(x/10²⁷)`. The pre-floor accumulator brackets `E` unconditionally
(`accumReal_over`/`accumReal_under`: the cert `Floor.CapsV` against the exact rational
`ê = NUM/DEN`, folded with the octave `2^k`, plus the reduced-argument and Horner-`sdiv`
truncation envelopes the `MARGIN` absorbs), and below the clamp the target satisfies `E < 1`
(`belowC_target_lt_one`), so the global brackets hold with no analytic hypothesis. -/

/-- Global floor-or-one-less bracket. -/
example (x : Nat) (hx : x < 2 ^ 256)
    (hC0 : FormalYul.Preservation.int256 x < FormalYul.Preservation.int256 C0thresh) :
    ∃ r, run_exp_ray_to_wad_evm x = .ok r ∧ ExpRealSpec.FloorOrOneLessBracket
      (FormalYul.Preservation.int256 x) (FormalYul.Preservation.int256 r) :=
  run_exp_ray_to_wad_evm_floorOrOneLess_uncond x hx hC0

/-- info: 'ExpYul.run_exp_ray_to_wad_evm_floorOrOneLess_uncond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_exp_ray_to_wad_evm_floorOrOneLess_uncond

/-- One-unit underestimation bound. -/
example (x : Nat) (hx : x < 2 ^ 256)
    (hC0 : FormalYul.Preservation.int256 x < FormalYul.Preservation.int256 C0thresh) :
    ∃ r, run_exp_ray_to_wad_evm x = .ok r ∧ ExpRealSpec.UnderByAtMostOne
      (FormalYul.Preservation.int256 x) (FormalYul.Preservation.int256 r) :=
  run_exp_ray_to_wad_evm_underByAtMostOne_uncond x hx hC0

/-- info: 'ExpYul.run_exp_ray_to_wad_evm_underByAtMostOne_uncond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_exp_ray_to_wad_evm_underByAtMostOne_uncond

/-! ## Discharged ingredients

Proved directly and axiom-clean:

* `tTree_in_cert_domain` — the runtime reduced argument stays in the certificate domain
  `|tTree x| ≤ H128`, so the Taylor caps (`Floor.CapsV`) instantiate at `t := tTree x`;
* `evTree_bracket` / `odTree_bracket` — the Horner-truncation bridge: the runtime even/odd
  accumulators bracket the exact integer polynomials `evNumV`/`odNumV` (in `v = vTree x`) within `2`
  units at the cleared scales `2^553`/`2^530`;
* `belowC_target_lt_one` — below the clamp boundary the target satisfies `E < 1`;
* `accumReal_over` / `accumReal_under` — the pre-floor accumulator never exceeds `E` and lies
  within one output unit below it. -/
example {x : Nat} (hx : x < 2 ^ 256)
    (hC : FormalYul.Preservation.int256 Cmask < FormalYul.Preservation.int256 x)
    (hC0 : FormalYul.Preservation.int256 x < FormalYul.Preservation.int256 C0thresh) :
    -(117932881612756647068972071382077242199 : Int) ≤ FormalYul.Preservation.int256 (tTree x) ∧
      FormalYul.Preservation.int256 (tTree x) ≤ 117932881612756647068972071382077242199 :=
  tTree_in_cert_domain hx hC hC0

/-- info: 'ExpYul.tTree_in_cert_domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tTree_in_cert_domain

/-- info: 'ExpYul.evTree_bracket' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evTree_bracket

/-- info: 'ExpYul.odTree_bracket' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms odTree_bracket

/-- info: 'ExpYul.belowC_target_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms belowC_target_lt_one

/-- info: 'ExpYul.accumReal_over' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms accumReal_over

/-- info: 'ExpYul.accumReal_under' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms accumReal_under

/-! ## The `lnWadToRay` round trip

For `w` with `w/10¹⁸ ∈ [1/√2, √2)`, the compiled composition
`expRayToWad(lnWadToRay(w))` returns `w − 1`, and returns `w` at the scale point
`w = 10¹⁸`. The proof composes the verified `lnWadToRay` runtime (`LnProof`) with the exp runtime. -/

/-- The `lnWadToRay` round trip. For `w` on the central band (`Wlo ≤ w ≤ Whi`, i.e.
`w/10¹⁸ ∈ [1/√2, √2)`), the runtime composition returns `w − 1`, and `w` at the scale point. -/
example {w : Nat} (hlo : Wlo ≤ w) (hhi : w ≤ Whi) :
    ∃ x r : Nat, LnYul.run_ln_wad_to_ray_evm w = .ok x ∧ run_exp_ray_to_wad_evm x = .ok r ∧
      (r : Int) = if w = 10 ^ 18 then (w : Int) else (w : Int) - 1 :=
  run_exp_ray_to_wad_evm_lnWadToRay_roundTrip_if hlo hhi

/-- info: 'ExpYul.run_exp_ray_to_wad_evm_lnWadToRay_roundTrip_if' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_exp_ray_to_wad_evm_lnWadToRay_roundTrip_if

end ExpYul

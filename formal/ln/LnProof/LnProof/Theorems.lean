import LnProof.Correct
import LnProof.ErrorBoundRuntime

/-!
# `lnWad` — proven properties of the compiled runtime (signpost)

This file is the at-a-glance demonstration that every documented property holds
for *the interpretation of the implementation*: the EVMYulLean execution of the
compiled `LnWrapper` Yul, `run_ln_wad_to_ray_evm` / `run_ln_wad_evm` (defined in
the generated `LnYulRuntime`). Each property below is a runtime-level theorem;
the axiom gate at the bottom pins every one of them to Lean's three standard
axioms, so a stray `sorry` (or any new axiom) breaks the build.

## The proof in four seams

```
 compiled Yul runtime     run_ln_wad_to_ray_evm        (LnYulRuntime, generated)
        │  seam 1: runtime ↔ model        run_ln_wad_to_ray_evm_eq_body   (Seam.RuntimeModel)
 hand model               lnWadToRayBody               (Model.Body)
        │  seam 2: model ⊨ floor/cut spec  lnWadToRayBody_floor / _cut_spec (Floor.Spec, Floor.CutEquiv)
 floor-cut spec           FloorSpecA / FloorSpecB      (Floor.Spec)
        │  seam 3: floor ↔ arithmetized cut  FloorSpec_iff_cutLnWadRayBracket (Floor.CutEquiv)
 real-free cut spec       CutLnWadRayBracket           (Spec.Cut)
        │  seam 4: cut ↔ Real.log          cutLnWadRayBracket_real          (Seam.RealLog)
 public target            LnWadToRaySpec               (Spec.Real, the Real.log bracket)
```

## Documented properties (all about the runtime)

| Property                              | Theorem                                      |
|---------------------------------------|----------------------------------------------|
| Correct vs. `Real.log` bracket (ray)  | `lnWadToRayRuntimeCorrect`                   |
| Correct vs. `Real.log` bracket (wad)  | `lnWadRuntimeCorrect`                        |
| `1.6986`-ulp upper error bound (ray)  | `lnWadToRayRuntimeErrorBound`                |
| Monotone in the input (ray / wad)     | `lnWadToRayRuntimeMono` / `lnWadRuntimeMono` |
| Reverts on nonpositive input          | `lnWadToRayRuntimeRevertsNonpositive_holds`  |
| Sign matches `x ⋛ 1`                  | `lnWadToRayRuntimeNegativeIff`               |
| `ln(1) = 0` at the wad scale-point    | `run_ln_wad_to_ray_evm_zero_at_wad`          |
| Equals the wrapper ABI dispatch       | `run_ln_wad_to_ray_evm_eq_callWord`          |

The public proofs live in `Correct` (correctness, monotonicity, reverts,
sign, zero) and `ErrorBoundRuntime` (the error bound). This file only restates
the headline guarantees explicitly and runs the axiom gate.
-/

namespace LnYul

open FormalYul
open FormalYul.Preservation

noncomputable section

/-- Ray output: floored against the `Real.log` fixed-point bracket. -/
example (x : Nat) (hx : x < 2 ^ 256) : LnWadToRayRuntimeCorrect x :=
  lnWadToRayRuntimeCorrect x hx

/-- Wad output: floored against the `Real.log` fixed-point bracket. -/
example (x : Nat) (hx : x < 2 ^ 256) : LnWadRuntimeCorrect x :=
  lnWadRuntimeCorrect x hx

/-- Ray output: strict upper error bound `10^27·log(x/10^18) < r + 1.6986`. -/
example (x : Nat) (hx : x < 2 ^ 256) :
    signedPositiveInput x →
      ∃ r, runLnWadToRaySigned x = .ok r ∧
        LnFloorCert.CutLogWadRayLtRational x r
          LnFloorCert.lnErrorBoundNum LnFloorCert.lnErrorBoundDen :=
  lnWadToRayRuntimeErrorBound x hx

/-- Ray output: monotone non-decreasing over ordered positive inputs. -/
example (x y : Nat) (hx : 0 < x) (hxy : x ≤ y) (hy : y < 2 ^ 255) :
    ∃ rx ry, runLnWadToRaySigned x = .ok rx ∧ runLnWadToRaySigned y = .ok ry ∧ rx ≤ ry :=
  lnWadToRayRuntimeMono x y hx hxy hy

/-- Nonpositive signed input reverts. -/
example (x : Nat) : LnWadToRayRuntimeRevertsNonpositive x :=
  lnWadToRayRuntimeRevertsNonpositive_holds x

end

end LnYul

/-!
## Axiom gate

`#guard_msgs in #print axioms` pins each public runtime theorem to Lean's
standard `propext`, `Classical.choice`, `Quot.sound`. The build fails if a proof
starts depending on anything more — a stray `sorry` introduces `sorryAx` and
breaks this gate.
-/

/-- info: 'LnYul.lnWadToRayRuntimeCorrect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LnYul.lnWadToRayRuntimeCorrect

/-- info: 'LnYul.lnWadRuntimeCorrect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LnYul.lnWadRuntimeCorrect

/-- info: 'LnYul.lnWadToRayRuntimeErrorBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LnYul.lnWadToRayRuntimeErrorBound

/-- info: 'LnYul.lnWadToRayRuntimeCorrect_of_cutCorrect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LnYul.lnWadToRayRuntimeCorrect_of_cutCorrect

/-- info: 'LnYul.lnWadRuntimeCorrect_of_cutCorrect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LnYul.lnWadRuntimeCorrect_of_cutCorrect

/-- info: 'LnYul.run_ln_wad_evm_eq_callWord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LnYul.run_ln_wad_evm_eq_callWord

/-- info: 'LnYul.run_ln_wad_to_ray_evm_eq_callWord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LnYul.run_ln_wad_to_ray_evm_eq_callWord

/-- info: 'LnYul.lnWadToRayRuntimeRevertsNonpositive_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LnYul.lnWadToRayRuntimeRevertsNonpositive_holds

/-- info: 'LnYul.lnWadRuntimeRevertsNonpositive_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LnYul.lnWadRuntimeRevertsNonpositive_holds

/-- info: 'LnYul.run_ln_wad_to_ray_evm_zero_at_wad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LnYul.run_ln_wad_to_ray_evm_zero_at_wad

/-- info: 'LnYul.run_ln_wad_evm_zero_at_wad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LnYul.run_ln_wad_evm_zero_at_wad

/-- info: 'LnYul.lnWadToRayRuntimeNegativeIff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LnYul.lnWadToRayRuntimeNegativeIff

/-- info: 'LnYul.lnWadRuntimeNegativeIff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LnYul.lnWadRuntimeNegativeIff

/-- info: 'LnYul.lnWadToRayRuntimeMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LnYul.lnWadToRayRuntimeMono

/-- info: 'LnYul.lnWadRuntimeMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LnYul.lnWadRuntimeMono

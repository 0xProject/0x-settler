import ExpProof.Seam.Revert
import ExpProof.Seam.Value
import ExpProof.Mono
import ExpProof.Mono.SeamR0
import ExpProof.Floor.PublicUncond
import ExpProof.Floor.R0BoundHolds
import ExpProof.Floor.R0Bound
import ExpProof.Floor.RoundTrip
import ExpProof.Mul.Shell
import ExpProof.Mul.Accum

/-!
# `expRayToWad` and `mulExpRay` — compiled-runtime proof signpost

This file is the at-a-glance demonstration that the documented properties hold for *the
interpretation of the implementation*: the EVMYulLean execution of the compiled `ExpWrapper` Yul,
`run_exp_ray_to_wad_evm` and `run_mul_exp_ray_evm` (defined in the generated `ExpYulRuntime`).
Each listed theorem is a runtime-level theorem or a runtime proof obligation; the axiom gate at the
bottom pins it to Lean's three standard axioms, so a stray `sorry` (or any new axiom) breaks the
build.

## Documented `expRayToWad` properties (about the runtime)

| Property                                          | Theorem                                          |
|---------------------------------------------------|--------------------------------------------------|
| Reverts on inputs ≥ `0x92b2f16cc66c5a4ae96e80d4`  | `run_exp_ray_to_wad_evm_revert`                  |
| Scale point: `expRayToWad(0) = 10^18`             | `run_exp_ray_to_wad_evm_zero`                    |
| Value path reduces to the `evm*` tree             | `run_exp_ray_to_wad_evm_eq_tree`                 |
| Never over / floor-or-one-less: `r ≤ E < r + 2`   | `run_exp_ray_to_wad_evm_floorOrOneLess_uncond`   |
| Underestimates by at most one: `⌊E⌋ − 1 ≤ r`      | `run_exp_ray_to_wad_evm_underByAtMostOne_uncond` |
| Monotone in the input                             | `run_exp_ray_to_wad_evm_mono_unconditional`      |
| `lnWadToRay` round trip                           | `run_exp_ray_to_wad_evm_lnWadToRay_roundTrip_if` |

Every `expRayToWad` property is unconditional. The monotonicity analytic core (`RegionMonotonicityFacts`,
reduced to the octave-seam `r0` doubling bound `SeamR0Bound`) is discharged by
`seamR0Bound_holds`; the floor brackets consume the discharged accumulator facts
(`accumReal_over`, `accumReal_under`, `belowC_target_lt_one`) directly.

The supported-range threshold is `0x92b2f16cc66c5a4ae96e80d4`; at or above it (and below `2^255`,
i.e. for any non-negative `int256` that large) the wrapper run halts with `revert`. At the scale
point `x = 0` the run returns the wad unit `10^18` exactly. For any signed input strictly below the
threshold the run returns the inline `evm*` arithmetic tree (the handle for the floor/monotone/bound
properties), reduced with no hand model.
-/

namespace ExpYul

open FormalYul

/-- Reverts above the supported range. -/
example (x : Nat)
    (h1 : (0x92b2f16cc66c5a4ae96e80d4 : Nat) ≤ FormalYul.u256 x)
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
per-point real bracket `r0Tree x ≈ (10¹⁸·2⁶⁸)·exp(rt)` and the seam relation `exp(rt1) =
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

/-! ## `mulExpRay`

The public spec for `mulExpRay` is a signed magnitude bracket plus monotonicity predicates in both
arguments. Discharged today, axiom-clean:

| Property                                            | Theorem                                 |
|-----------------------------------------------------|-----------------------------------------|
| Exact value/panic partition of canonical calldata   | `mulExpRay_value_iff_not_panic`         |
| Guard word ↔ domain bridge                          | `valueDomain_iff_guard_eq_zero`         |
| Value path returns the compiled tree                | `run_mul_exp_ray_evm_eq_tree`           |
| Rejected inputs revert                              | `run_mul_exp_ray_evm_revert`            |
| Signed bracket `0 ≤ m ≤ A < m + 2` on the domain    | `mulExpRay_run_bracket`                 |
| Result magnitude is `⌊A⌋` or `⌊A⌋ − 1`              | `mulExpRay_run_floor_membership`        |
| `A < 1` pins the result to zero                     | `mulExpRay_run_pins_zero`               |
| Zero multiplier returns zero (and its bracket)      | `run_mul_exp_ray_evm_zero_of_guard`     |
| Scale point `mulExpRay(y, 0) = y` (and its bracket) | `run_mul_exp_ray_evm_scale_point`       |
| Zero clamp at deep-negative `x` (and its bracket)   | `run_mul_exp_ray_evm_clamped`           |

The bracket is proven on the whole value domain: the scale-symbolic per-point certificates
(`r0Scaled_real_over_within`/`r0Scaled_real_under_within`) instantiate at the dynamic scale
`abs(y)·2ˢ ∈ [2¹²⁵, 10¹⁸·2⁶⁷]`, and the accumulator fold (`Mul.Accum`) closes the live region.
Still open, visible below as explicit hypotheses of the facade lemmas: the runtime monotonicity
statements.
-/

/-- Canonical `mulExpRay` inputs are partitioned by the implementation value and panic guards. -/
example {y x : Nat} (hcanon : MulExpRayCanonical y x) :
    MulExpRayValueDomain y x ∨ MulExpRayPanicDomain y x :=
  mulExpRay_value_or_panic_of_canonical hcanon

/-- **The signed bracket on the whole value domain.** Every accepted input returns a result whose
magnitude `m` satisfies `0 ≤ m ≤ A ∧ A < m + 2` for `A = abs(y)·exp(x/10²⁷)`. -/
example {y x : Nat} (h : MulExpRayValueDomain y x) : MulExpRayRunBracket y x :=
  mulExpRay_run_bracket h

/-- **Floor membership.** Every accepted input's result magnitude is `⌊A⌋` or `⌊A⌋ − 1`. -/
example {y x : Nat} (h : MulExpRayValueDomain y x) :
    ∃ r, run_mul_exp_ray_evm y x = .ok r ∧
      ((if FormalYul.Preservation.int256 y < 0
          then -(FormalYul.Preservation.int256 r) else FormalYul.Preservation.int256 r) =
          ⌊ExpRealSpec.mulExpRayMagnitudeTarget (FormalYul.Preservation.int256 y)
            (FormalYul.Preservation.int256 x)⌋ ∨
        (if FormalYul.Preservation.int256 y < 0
          then -(FormalYul.Preservation.int256 r) else FormalYul.Preservation.int256 r) =
          ⌊ExpRealSpec.mulExpRayMagnitudeTarget (FormalYul.Preservation.int256 y)
            (FormalYul.Preservation.int256 x)⌋ - 1) :=
  mulExpRay_run_floor_membership h

/-- The value and panic guards are disjoint on canonical inputs. -/
example {y x : Nat} (hcanon : MulExpRayCanonical y x) :
    MulExpRayValueDomain y x ↔ ¬ MulExpRayPanicDomain y x :=
  mulExpRay_value_iff_not_panic hcanon

/-- A tree equality plus a tree bracket gives the public runtime bracket spec. -/
example {y x : Nat}
    (hrun : run_mul_exp_ray_evm y x = .ok (mulExpTree y x))
    (hbracket : ExpRealSpec.MulExpRayBracket
      (FormalYul.Preservation.int256 y) (FormalYul.Preservation.int256 x)
      (FormalYul.Preservation.int256 (mulExpTree y x))) :
    MulExpRayRunBracket y x :=
  mulExpRay_run_bracket_of_tree hrun hbracket

/-- A tree equality plus ordered tree results gives the public runtime monotonicity-in-`x` spec. -/
example {y x1 x2 : Nat}
    (hrun1 : run_mul_exp_ray_evm y x1 = .ok (mulExpTree y x1))
    (hrun2 : run_mul_exp_ray_evm y x2 = .ok (mulExpTree y x2))
    (hmono : ExpRealSpec.MulExpRaySignedMonotone
      (FormalYul.Preservation.int256 y) (FormalYul.Preservation.int256 x1)
      (FormalYul.Preservation.int256 x2) (FormalYul.Preservation.int256 (mulExpTree y x1))
      (FormalYul.Preservation.int256 (mulExpTree y x2))) :
    MulExpRayRunMonotone y x1 x2 :=
  mulExpRay_run_monotone_of_tree hrun1 hrun2 hmono

/-- A tree equality plus ordered tree results gives the public runtime monotonicity-in-`y` spec. -/
example {y1 y2 x : Nat}
    (hrun1 : run_mul_exp_ray_evm y1 x = .ok (mulExpTree y1 x))
    (hrun2 : run_mul_exp_ray_evm y2 x = .ok (mulExpTree y2 x))
    (hmono : ExpRealSpec.MulExpRayYMonotone
      (FormalYul.Preservation.int256 y1) (FormalYul.Preservation.int256 y2)
      (FormalYul.Preservation.int256 x) (FormalYul.Preservation.int256 (mulExpTree y1 x))
      (FormalYul.Preservation.int256 (mulExpTree y2 x))) :
    MulExpRayRunYMonotone y1 y2 x :=
  mulExpRay_run_y_monotone_of_tree hrun1 hrun2 hmono

/-- A tree equality plus sign-aware ordered tree results gives the joint runtime spec. -/
example {y1 y2 x1 x2 : Nat}
    (hrun1 : run_mul_exp_ray_evm y1 x1 = .ok (mulExpTree y1 x1))
    (hrun2 : run_mul_exp_ray_evm y2 x2 = .ok (mulExpTree y2 x2))
    (hmono : ExpRealSpec.MulExpRayJointMonotone
      (FormalYul.Preservation.int256 y1) (FormalYul.Preservation.int256 y2)
      (FormalYul.Preservation.int256 x1) (FormalYul.Preservation.int256 x2)
      (FormalYul.Preservation.int256 (mulExpTree y1 x1))
      (FormalYul.Preservation.int256 (mulExpTree y2 x2))) :
    MulExpRayRunJointMonotone y1 y2 x1 x2 :=
  mulExpRay_run_joint_monotone_of_tree hrun1 hrun2 hmono

/-- Zero magnitude satisfies the signed bracket for every exponent. -/
example (x : Int) : ExpRealSpec.MulExpRayBracket 0 x 0 :=
  mulExpRayBracket_zero_result x

/-- The value path returns the compiled arithmetic tree whenever the guard word is zero. -/
example (y x : Nat) (hguard : mulExpGuardTree y x = 0) :
    run_mul_exp_ray_evm y x = .ok (mulExpTree y x) :=
  run_mul_exp_ray_evm_eq_tree_of_guard y x hguard

/-- The compiled runtime returns zero for a zero multiplier whenever the guard accepts. -/
example (x : Nat) (hguard : mulExpGuardTree 0 x = 0) : run_mul_exp_ray_evm 0 x = .ok 0 :=
  run_mul_exp_ray_evm_zero_of_guard x hguard

/-- The compiled runtime satisfies the public bracket spec at zero magnitude whenever the guard
accepts. -/
example (x : Nat) (hguard : mulExpGuardTree 0 x = 0) : MulExpRayRunBracket 0 x :=
  mulExpRay_run_bracket_zero x hguard

/-- The guard word is zero exactly on the value domain. -/
example {y x : Nat} (hcanon : MulExpRayCanonical y x) :
    MulExpRayValueDomain y x ↔ mulExpGuardTree y x = 0 :=
  valueDomain_iff_guard_eq_zero hcanon

/-- Accepted inputs return the compiled tree. -/
example {y x : Nat} (h : MulExpRayValueDomain y x) :
    run_mul_exp_ray_evm y x = .ok (mulExpTree y x) :=
  run_mul_exp_ray_evm_eq_tree h

/-- Rejected inputs revert. -/
example {y x : Nat} (h : MulExpRayPanicDomain y x) :
    run_mul_exp_ray_evm y x = .error "revert" :=
  run_mul_exp_ray_evm_revert h

/-- The scale point returns the multiplier exactly. -/
example {y : Nat} (hy : y < 2 ^ 256) (habs : absTree y ≤ scaleQ67) :
    run_mul_exp_ray_evm y 0 = .ok y :=
  run_mul_exp_ray_evm_scale_point hy habs

/-- The scale-point result satisfies the public bracket. -/
example {y : Nat} (hy : y < 2 ^ 256) (habs : absTree y ≤ scaleQ67) :
    MulExpRayRunBracket y 0 :=
  mulExpRay_run_bracket_scale_point hy habs

/-- At or below the zero cutoff, every supported magnitude returns zero. -/
example {y x : Nat} (hy : y < 2 ^ 256) (hx : x < 2 ^ 256)
    (habs : absTree y ≤ scaleQ67)
    (hclamp : FormalYul.Preservation.int256 x ≤ FormalYul.Preservation.int256 mulExpRayZeroMax) :
    run_mul_exp_ray_evm y x = .ok 0 :=
  run_mul_exp_ray_evm_clamped hy hx habs hclamp

/-- The clamped result satisfies the public bracket. -/
example {y x : Nat} (hy : y < 2 ^ 256) (hx : x < 2 ^ 256)
    (habs : absTree y ≤ scaleQ67)
    (hclamp : FormalYul.Preservation.int256 x ≤ FormalYul.Preservation.int256 mulExpRayZeroMax) :
    MulExpRayRunBracket y x :=
  mulExpRay_run_bracket_clamped hy hx habs hclamp

/-- The accumulator floor and target bounds imply the public magnitude bracket. -/
example {y x m : Int} {A : Real}
    (hm_nonneg : 0 ≤ m)
    (hfloor : (m : Real) ≤ A)
    (hfloor1 : A < (m : Real) + 1)
    (hover : A ≤ ExpRealSpec.mulExpRayMagnitudeTarget y x)
    (hunder : ExpRealSpec.mulExpRayMagnitudeTarget y x < A + 1) :
    ExpRealSpec.MulExpRayMagnitudeBracket y x m :=
  mulExpRayMagnitudeBracket_of_accum hm_nonneg hfloor hfloor1 hover hunder

/-- Sign reapplication turns a magnitude bracket into the signed public bracket. -/
example {y x r m : Int}
    (hmag : ExpRealSpec.MulExpRayMagnitudeBracket y x m)
    (hsign : if y < 0 then r = -m else r = m) :
    ExpRealSpec.MulExpRayBracket y x r :=
  mulExpRayBracket_of_signed_magnitude hmag hsign

/-- Magnitude brackets imply the magnitude is under by at most one output unit. -/
example {y x m : Int}
    (h : ExpRealSpec.MulExpRayMagnitudeBracket y x m) :
    ⌊ExpRealSpec.mulExpRayMagnitudeTarget y x⌋ - 1 ≤ m :=
  mulExpRayMagnitudeBracket_to_underByAtMostOne h

/-- Existing `expRayToWad` floor brackets instantiate the `y = 10^18` specialization. -/
example {x r : Int} (hr : 0 ≤ r)
    (h : ExpRealSpec.FloorOrOneLessBracket x r) :
    ExpRealSpec.MulExpRayBracket (10 ^ 18) x r :=
  floorOrOneLess_to_mulExpRayBracket_wad hr h

/-- The real target is monotone in the exponent with direction determined by the multiplier sign. -/
example {y x1 x2 : Int} (hle : x1 ≤ x2) :
    if y < 0 then ExpRealSpec.mulExpRayTarget y x2 ≤ ExpRealSpec.mulExpRayTarget y x1
    else ExpRealSpec.mulExpRayTarget y x1 ≤ ExpRealSpec.mulExpRayTarget y x2 :=
  ExpRealSpec.mulExpRayTarget_signed_mono hle

/-- The real target is monotone in the multiplier. -/
example {y1 y2 x : Int} (hle : y1 ≤ y2) :
    ExpRealSpec.mulExpRayTarget y1 x ≤ ExpRealSpec.mulExpRayTarget y2 x :=
  ExpRealSpec.mulExpRayTarget_mono_y hle

/-- The real target is sign-aware jointly monotone in the multiplier and exponent. -/
example {y1 y2 x1 x2 : Int}
    (h :
      (0 ≤ y1 ∧ y1 ≤ y2 ∧ x1 ≤ x2) ∨
      (y1 ≤ y2 ∧ y2 ≤ 0 ∧ x2 ≤ x1) ∨
      (y1 ≤ 0 ∧ 0 ≤ y2)) :
    ExpRealSpec.mulExpRayTarget y1 x1 ≤ ExpRealSpec.mulExpRayTarget y2 x2 :=
  ExpRealSpec.mulExpRayTarget_joint_mono h

/-- info: 'ExpYul.mulExpRay_run_bracket' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mulExpRay_run_bracket

/-- info: 'ExpYul.mulExpRay_run_floor_membership' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mulExpRay_run_floor_membership

/-- info: 'ExpYul.mulExpRay_run_pins_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mulExpRay_run_pins_zero

/-- info: 'ExpYul.mulExpRay_run_bracket_of_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mulExpRay_run_bracket_of_tree

/-- info: 'ExpYul.mulExpRay_run_monotone_of_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mulExpRay_run_monotone_of_tree

/-- info: 'ExpYul.mulExpRay_run_y_monotone_of_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mulExpRay_run_y_monotone_of_tree

/-- info: 'ExpYul.mulExpRay_run_joint_monotone_of_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mulExpRay_run_joint_monotone_of_tree

/-- info: 'ExpYul.mulExpRay_value_or_panic_of_canonical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mulExpRay_value_or_panic_of_canonical

/-- info: 'ExpYul.mulExpRay_value_iff_not_panic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mulExpRay_value_iff_not_panic

/-- info: 'ExpYul.mulExpRayMagnitudeBracket_of_accum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mulExpRayMagnitudeBracket_of_accum

/-- info: 'ExpYul.mulExpRayBracket_of_signed_magnitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mulExpRayBracket_of_signed_magnitude

/-- info: 'ExpYul.mulExpRayMagnitudeBracket_to_underByAtMostOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mulExpRayMagnitudeBracket_to_underByAtMostOne

/-- info: 'ExpYul.mulExpRayBracket_zero_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mulExpRayBracket_zero_result

/-- info: 'ExpYul.run_mul_exp_ray_evm_eq_tree_of_guard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_mul_exp_ray_evm_eq_tree_of_guard

/-- info: 'ExpYul.run_mul_exp_ray_evm_zero_of_guard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_mul_exp_ray_evm_zero_of_guard

/-- info: 'ExpYul.mulExpRay_run_bracket_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mulExpRay_run_bracket_zero

/-- info: 'ExpYul.valueDomain_iff_guard_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms valueDomain_iff_guard_eq_zero

/-- info: 'ExpYul.run_mul_exp_ray_evm_eq_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_mul_exp_ray_evm_eq_tree

/-- info: 'ExpYul.run_mul_exp_ray_evm_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_mul_exp_ray_evm_revert

/-- info: 'ExpYul.run_mul_exp_ray_evm_scale_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_mul_exp_ray_evm_scale_point

/-- info: 'ExpYul.mulExpRay_run_bracket_scale_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mulExpRay_run_bracket_scale_point

/-- info: 'ExpYul.run_mul_exp_ray_evm_clamped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_mul_exp_ray_evm_clamped

/-- info: 'ExpYul.mulExpRay_run_bracket_clamped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mulExpRay_run_bracket_clamped

/-- info: 'ExpRealSpec.mulExpRayTarget_signed_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ExpRealSpec.mulExpRayTarget_signed_mono

/-- info: 'ExpRealSpec.mulExpRayTarget_mono_y' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ExpRealSpec.mulExpRayTarget_mono_y

/-- info: 'ExpRealSpec.mulExpRayTarget_joint_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ExpRealSpec.mulExpRayTarget_joint_mono

/-! ## `Real.exp` floor brackets

Each bracket is stated on the runtime result `r` (`run_exp_ray_to_wad_evm x = .ok r`) against the
target `E = 10¹⁸·exp(x/10²⁷)`. The pre-floor accumulator brackets `E` unconditionally
(`accumReal_over`/`accumReal_under`: the cert `Floor.CapsV` against the exact rational
`ê = NUM/DEN`, folded with the octave `2^k`, plus the argument-granularity, reduced-argument and
Horner-`div` truncation envelopes the `MARGIN` absorbs), and below the clamp the target satisfies
`E < 1`
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
  `|tTree x| ≤ H129`, so the Taylor caps (`Floor.CapsV`) instantiate at `t := tTree x`;
* `evTree_bracket` / `odTree_bracket` — the Horner-truncation bridge: the runtime even/odd
  accumulators bracket the exact integer polynomials `evNumV`/`odNumV` (in `v = vTree x`) within
  `≈1.008`/`≈1.002` units at the cleared scales `2^528`/`2^510`;
* `belowC_target_lt_one` — below the clamp boundary the target satisfies `E < 1`;
* `accumReal_over` / `accumReal_under` — the pre-floor accumulator never exceeds `E` and lies
  within one output unit below it. -/
example {x : Nat} (hx : x < 2 ^ 256)
    (hC : FormalYul.Preservation.int256 Cmask < FormalYul.Preservation.int256 x)
    (hC0 : FormalYul.Preservation.int256 x < FormalYul.Preservation.int256 C0thresh) :
    -(235865763225513294137944142764154484399 : Int) ≤ FormalYul.Preservation.int256 (tTree x) ∧
      FormalYul.Preservation.int256 (tTree x) ≤ 235865763225513294137944142764154484399 :=
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

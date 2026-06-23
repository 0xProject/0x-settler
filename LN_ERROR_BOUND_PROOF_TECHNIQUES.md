# Ln Error Bound Proof Techniques

This note records the Lean proof techniques investigated for the
`1.688558253` ulp `lnWadToRay` upper error bound, along with the outcomes of
the experiments so far.

The target theorem is:

```lean
model_ln_wad_error_bound_1_688558253
```

in `formal/ln/LnProof/LnProof/ErrorBound.lean`. The theorem is intended to
prove:

```lean
let r := toInt (model_ln_wad_evm x)
CutLeLogWadRay r x ∧
  CutLogWadRayLtRational x r 1688558253 1000000000
```

for `1 <= x < 2^255`.

The current bottleneck is the positive-shift upper proof. The negative-shift
and `c = 160` routes are already handled by existing cap algebra. The remaining
proof obligations are the global positive-shift phase cover checks:

```lean
positive_shift_ge_phase_cover_all
positive_shift_lt_phase_cover_all
```

Those currently ask the Lean kernel to reduce large boolean searches over
`sumGEB 320`. That is too slow for CI and, more importantly, the current
interval shape is structurally too conservative: the phase cells advance by
only a few dozen mantissas while the positive-shift domain is about `2^95`
mantissas wide.

## Constraints

- Do not change production Solidity.
- Keep the proof tied to the generated Yul/EVMYulLean model.
- Do not introduce `native_decide`.
- Do not use `pkill` or `killall`.
- Current work is in `/home/user/Documents/git-repos/0x-settler-lnwad-error-bound`.
- The exact rational bound is `1688558253 / 1000000000`.
- Current proof work is Lean-only; no new Python generators or fuzzing should
  be added for this phase.

## Current File State

The exact-bound proof is split across:

```lean
LnProof.ErrorBoundCore
LnProof.ErrorBound
```

`LnProof.ErrorBoundCore` contains the real-free cut definitions, cap algebra,
branch certificate predicates, and soundness lemmas. It checks independently.

`LnProof.ErrorBound` contains the public theorem:

```lean
model_ln_wad_error_bound_1_688558253
```

The tail theorem is blocked only by replacing:

```lean
positive_shift_ge_phase_cover_all
positive_shift_lt_phase_cover_all
```

with a compact Lean-checked global certificate. The later assembly of
`model_ln_wad_error_bound_1_688558253` is not where the blow-up occurs.

## Existing Proof Decomposition

The current exact-bound proof decomposes the positive-shift upper cut into:

1. A coarse residue route:

   ```lean
   PosShiftResidueOk m c r
   ```

   This is enough to reuse the existing cap algebra through
   `lo_ge_pos_exact` and `lo_lt_pos_exact`.

2. A phase/direct route:

   ```lean
   PosShiftGePhaseDirectOk 320 m c
   PosShiftLtPhaseDirectOk 320 m c
   ```

   This proves the required cap directly by a 320-term exponential lower sum.

3. A direct-residue gap route:

   ```lean
   PosShiftDirectResidueGapOk m c r
   PosShiftGePhaseGapDirectOk 320 m c
   PosShiftLtPhaseGapDirectOk 320 m c
   ```

   This is the route needed for the exact staircase witness cases where the
   coarse residue predicate fails but a smaller direct floor gap still holds.

Relevant constants:

```lean
lnErrorCoarsePosResidue := 11562080766880751500032140603279015936
lnErrorDirectResidueGap := 336460000000000000
posResidueGapThreshold := 86144214621787901969
```

At the known hard witness, the direct gap is just above the direct threshold:

```text
posResidueGap = 336461008378301558
lnErrorDirectResidueGap = 336460000000000000
```

That is why a proof must capture the integer staircase effect. A smooth
envelope bound is not enough.

## Technique: Kernel Brute Force Phase Cover

The first approach was to let the kernel reduce:

```lean
(List.range 159).all
  (fun i => gePhaseCoverB phaseCoverFuel (i + 1) Sc (MHI - 1))

(List.range 159).all
  (fun i => ltPhaseCoverB phaseCoverFuel (i + 1) MLO (Sc - 1))
```

with `phaseCoverFuel := 20000` and `phaseSearchFuel := 128`.

Result:

- This reduction runs long enough that it is not viable for CI.
- A monitored full-file run of the current fast phase-cover version reached
  about `14.6 GB` RSS before exiting with status `137`. Treat that exit
  status as operational termination, not as a Lean diagnostic.
- A prefix check through the branch machinery, stopping immediately before the
  two global phase-cover facts, completed successfully. This localizes the
  blow-up to the global cover reductions rather than the supporting lemmas.
- A ge-cover-only probe was interrupted after it reached about `9 GB` RSS.
- A single-`c` ge-cover probe was interrupted after it reached about `10 GB`
  RSS. Splitting the same phase-cover predicate by `c` is therefore not a
  viable fix.
- A monolithic full check that exited with `137` was externally terminated by
  another process, so that exit is not evidence of a Lean failure, theorem
  counterexample, or broken Lean worker.
- A later bounded full check also exited via external termination before Lean
  produced diagnostic output. The user confirmed another agent had terminated
  it. Treat these exits as external process noise, not as counterexamples and
  not as Lean proof failures. They also should not be treated as evidence that
  the Lean process itself is crashing or hanging incorrectly. The remaining
  objection to this route is proof shape and CI cost, not an observed Lean
  diagnostic.
- Independent of those external terminations, the phase-cell width is far too
  small for a global cover with `phaseCoverFuel = 20000`. The exact endpoint
  probe gives:

  ```text
  ge width near Sc, c=1:       18
  ge width near Sc, c=159:     19
  lt width near MLO, c=1:      25
  lt width near MLO, c=159:    26
  ```

  The same widths were observed at sampled offsets `+10^6` and `+10^12`.
  These cells cannot cover a `2^95`-scale mantissa interval with a 20,000-step
  fuel limit.
- It also exposes a proof-shape problem: the interval cell check freezes the
  phase argument at the left endpoint and the target `posTopX` at the right
  endpoint. That is much stronger than the pointwise theorem.
- Sample diagnostic:

  ```text
  gePhaseCellOkB Sc (Sc + 10) 1 = true
  gePhaseCellOkB Sc (Sc + 100) 1 = false
  ```

- Pointwise checks can still be true at sampled points, so the failed wider
  interval cells do not disprove the theorem. They show that this particular
  interval abstraction is too lossy.
- A minimal fuel sanity check confirms the fast cover is a literal cell walk:

  ```lean
  #eval gePhaseCoverFastB 1 1 Sc (MHI - 1)  -- false
  #eval gePhaseCoverFastB 2 1 Sc (MHI - 1)  -- false
  #eval ltPhaseCoverFastB 1 1 MLO (Sc - 1)  -- false
  #eval ltPhaseCoverFastB 2 1 MLO (Sc - 1)  -- false
  ```

  Combined with the measured cell widths, this means the current global
  `phaseCoverFuel := 20000` facts cannot be salvaged by waiting longer: the
  boolean being asked of the kernel is not a compact full-domain certificate.
- A later fixed-offset Lean diagnostic confirmed that the old frozen-left
  reach stays narrow across the branch, not only at the edge:

  ```text
  ge c=1 reach at Sc, Sc+10^6, Sc+10^12, Sc+10^18, Sc+10^24:
    18, 18, 18, 18, 18
  ge c=1 reach at midpoint:
    27
  lt c=1 reach at MLO, MLO+10^6, MLO+10^12, MLO+10^18, MLO+10^24:
    25, 25, 25, 25, 25
  lt c=1 reach at midpoint:
    3
  ```

Conclusion: do not keep the global `decide +kernel` phase cover as the final
proof route. The issue is not the externally killed process; the current cover
predicate is the wrong global certificate.

When the two global phase-cover facts are temporarily replaced by axioms, the
suffix of the proof checks:

```text
model_ln_wad_positive_shift_ge_branch_cert_auto
model_ln_wad_positive_shift_lt_branch_cert_auto
```

The printed axiom footprint of each suffix theorem is exactly the corresponding
stubbed phase-cover fact plus the normal imported Lean footprint. This isolates
the current bottleneck to the phase-cover certificate, not the later public
theorem assembly.

## Technique: Arithmetic Top-Budget Route

The branch certificate also contains arithmetic top-budget alternatives:

```lean
PosShiftGeTopBudgetIneqOk m c
PosShiftLtTopBudgetIneqOk m c
```

Those avoid `sumGEB 320` entirely and reuse the already checked cap algebra in
`lo_ge_pos_budget_exact` and `lo_lt_pos_budget_exact`.

Lean-only threshold probes over the pointwise boolean predicates show that
this route covers most of the positive-shift domain:

```text
first ge top-budget true point for c = 74:  Sc + 22130385913351247477352
first ge top-budget true point for c = 98:  Sc + 1
first ge top-budget true point for c = 122: Sc + 1
first lt top-budget true point for c = 143: MLO + 30564499033846628872
```

The same probes confirm that the existing monotone coarse cell predicate using
only `minPosAvail` does not certify those suffixes:

```text
geTopBudgetCoarseCellOkB split (MHI - 1) c = false
ltTopBudgetCoarseCellOkB split (Sc - 1) c = false
```

Conclusion: top-budget arithmetic is useful, but the proof still needs a
residue-aware certificate. The pointwise top-budget predicate succeeds because
the accumulator residue and the smooth error do not maximize together; the
coarse monotone predicate deliberately discards that correlation and is too
weak.

## Technique: Faster `sumGEB` Recurrence

The original boolean sum check recomputed enough factorial and power structure
to be expensive. I introduced a recurrence that carries:

```lean
expNum n p q
fact n * q^n
p^n
```

in one state:

```lean
def expSumState (p q : Nat) : Nat -> Nat × Nat × Nat
```

and rewrote `sumGEB` to use it.

Result:

- Prefix elaboration through the local direct certificate improved from about
  43 seconds to about 36 seconds in the checks I ran.
- This is a useful local speedup.
- It is not enough to make the global phase-cover proof acceptable.

I also tested a tail-recursive evaluator:

```lean
expSumStateGo
expSumStateFast
```

and temporarily used it in `sumGEB`.

Result:

- `LnProof.ErrorBoundCore` still checked with the unused definitions.
- When `sumGEB` used the tail-recursive evaluator, the final file aborted
  quickly with:

  ```text
  Stack overflow detected. Aborting.
  ```

Conclusion: keep the current recurrence-backed `expSumState`, but do not use
the tail-recursive `expSumStateFast` evaluator for the kernel-reduced final
proof.

## Technique: Static Phase Cell Lists

I added a static cell-list checker:

```lean
structure PhaseCell where
  lo : Nat
  hi : Nat

def gePhaseCellListCoverB ...
def ltPhaseCellListCoverB ...
```

with soundness lemmas:

```lean
gePhaseCellListCoverB_sound
ltPhaseCellListCoverB_sound
```

Result:

- The checker and soundness lemmas elaborate.
- The existing phase cell predicate is still too conservative for large cells.
- A full cover using this predicate would require far too many tiny cells.

Conclusion: the static-list shape is sound and reusable, but the cell
predicate must become sharper before it can be a final global certificate.

## Technique: Top-Budget Thresholds

I checked whether the positive-shift top-budget predicate could be treated as
monotone in `m` for each `c`, which would make it possible to replace a large
cover by one threshold per branch.

Result:

- On the ge side, top budget succeeds on large ranges. For example, at `c = 6`
  a first true point was found around:

  ```text
  56022770974786142495047936484
  ```

- The predicate was not monotone enough to justify a simple bisection
  certificate.
- On the lt side, the same issue appears: the hard mantissa can fail while
  points near `Sc` pass.
- Exact endpoint checks show the pointwise top-budget branch is close but not
  globally sufficient by itself. At the lower ge edge `m = Sc`, the failing
  positive-shift buckets are:

  ```text
  c = 74, 98, 122
  ```

  At the lower lt edge `m = MLO`, the failing bucket is:

  ```text
  c = 143
  ```

  The same all-`c` endpoint checks pass at the upper branch edges
  `m = MHI - 1` and `m = Sc - 1`.
- The full branch certificate still succeeds at those failing top-budget
  endpoints, so the misses are not counterexamples. They are exactly the kind
  of modular/staircase pockets that need a direct witness route.

Conclusion:

- Top-budget checks are useful as pruning diagnostics.
- They should not be encoded as a one-threshold theorem unless a separate
  monotonicity proof is found.
- The endpoint failures identify the buckets where a compact direct or modular
  certificate has to do real work.

## Technique: Coarse Top-Budget Interval Cells

I added Lean-checked interval predicates:

```lean
geTopBudgetCoarseCellOkB
ltTopBudgetCoarseCellOkB
```

with soundness lemmas:

```lean
geTopBudgetCoarseCellOkB_sound
ltTopBudgetCoarseCellOkB_sound
```

These cells use a uniform lower bound on the available fractional margin:

```lean
minPosAvail := lnPhaseExtraArg + twoPow27N * lnErrorBoundDen
```

The proof comes from the exact decomposition:

```lean
lnErrArg r =
  phase * den + extra * 2^99 + residueGap * 2^27 * den
```

and the floor fact `1 <= residueGap`.

Result:

- The soundness lemmas check without `native_decide`.
- The axiom footprint is the normal imported footprint:

  ```text
  [propext, Classical.choice, Quot.sound]
  ```

- The cells are too conservative for the hard global cover because they only
  use the one-unit residue floor. Representative diagnostics:

  ```text
  geTopBudgetCoarseCellOkB Sc Sc 1 = false
  geTopBudgetCoarseCellOkB (MHI - 1) (MHI - 1) 1 = false
  geTopBudgetCoarseCellOkB Sc Sc 159 = false
  ```

Conclusion:

- Keep these cells as a cheap branch when they fire.
- They cannot replace the exact staircase witness, because the exact proof
  needs a much sharper lower bound on available residue than `1`.

## Technique: Constant-Tail Top-Budget Run Cells

I added a sharper top-budget interval predicate that keeps the output bucket
fixed over the cell and uses the cell's actual tail residue instead of the
global one-unit residue floor:

```lean
geTopBudgetRunCellOkB
ltTopBudgetRunCellOkB
```

with soundness lemmas:

```lean
geTopBudgetRunCellOkB_sound
ltTopBudgetRunCellOkB_sound
```

The checker proves that every point in `[lo, hi]` stays below the next
`2^72` accumulator boundary from the left endpoint:

```lean
posAccI hi c < (rlo + 1) * 2^72
```

Then it checks the endpoint budget with:

```lean
posAvailGe hi c rlo
posAvailLt hi c rlo
```

The soundness proof replays the constant-tail fact with
`lnTail_eq_of_residue_run` and uses monotonicity of `posTopX`, `posBaseY*`,
and `posPhaseNat*` to move from the endpoints to any interior `m`.

Result:

- `lake build LnProof.ErrorBoundCore` succeeds with these lemmas.
- The axiom footprint is the normal imported footprint:

  ```text
  [propext, Classical.choice, Quot.sound]
  ```

- I wired the predicates into the mixed branch-cell checker:

  ```lean
  geBranchCellOkB
  ltBranchCellOkB
  ```

- First-cell deterministic reach from the lower branch edges is still small:

  ```text
  geTopBudgetRun c=1:    Sc .. Sc+15
  geTopBudgetRun c=159:  Sc .. Sc+26
  ltTopBudgetRun c=1:    MLO .. MLO+18
  ltTopBudgetRun c=159:  MLO .. MLO+6
  ```

- After wiring the arm into the mixed branch checker, the representative
  first-cell reaches remain unchanged:

  ```text
  ge c=1:   Sc .. Sc+49
  ge c=74:  Sc .. Sc+18
  ge c=98:  Sc .. Sc+18
  ge c=122: Sc .. Sc+18
  lt c=1:   MLO .. MLO+63
  lt c=6:   MLO .. MLO+35
  lt c=143: MLO .. MLO+26
  ```

Conclusion:

- Keep the run-budget cells as a sound local branch. They are stronger than
  the global coarse top-budget cell when the bucket is fixed.
- They do not solve the global positive-shift proof. Near the lower hard edge,
  the same constant-tail/bucket-local limitation keeps cells small.

## Technique: Local Direct Cells

I added a local fallback:

```lean
def localDirectCell (m c : Nat) : PosShiftDirectCell :=
  { c := c, lo := max MLO (m - 16), hi := m, n := 320 }

def residueOrLocalDirectCertB (m c : Nat) (r : Int) : Bool :=
  residueGapOkB m c r || localDirectCertB m c
```

and proved:

```lean
residue_or_direct_of_local_certB
```

Result:

- The soundness proof works.
- It is useful for exact or near-exact hard witnesses.
- It does not solve the global proof because the direct cells are also small.
- Increasing `n` did not make wide direct cells work in the quick checks.

Conclusion: local direct cells are a good fallback for a small certified hard
set, not a global certificate by themselves.

I also wired exact direct top cells into the mixed branch certificate:

```lean
directTopCellOkB
PosShiftTopDirectOk 320 m c
```

This lets both ge and lt branch certificates use the existing direct exact
`lnErrArg (lnTail lo)` interval proof before falling back to phase or
direct-gap phase.

Result:

- The branch soundness lemmas still check with the normal imported axiom
  footprint.
- The first lower-edge reach improves slightly, but remains bucket-local:

  ```text
  ge c=1:   Sc .. Sc+49
  ge c=159: Sc .. Sc+72
  lt c=1:   MLO .. MLO+63
  lt c=159: MLO .. MLO+39
  ```

- Raising the direct sum length to `640` or `1024` did not widen the first ge
  cells in the diagnostic checks.

Conclusion:

- Keep direct top cells as a useful fallback witness.
- They do not change the main conclusion: a viable global proof needs a
  broader staircase-aware interval certificate, not just more Taylor terms.

## Technique: Mixed Branch Interval Walk

The current Lean file has mixed branch-cell predicates:

```lean
geBranchCellOkB
ltBranchCellOkB
```

These try residue-run cells, constant-tail residue cells, coarse top-budget
cells, constant-tail top-budget run cells, direct top cells, phase cells, and
direct-residue phase-gap cells in one sound interval predicate.

Result:

- The soundness lemmas check:

  ```lean
  geBranchCellOkB_sound
  ltBranchCellOkB_sound
  ```

- Deterministic lower-edge walks remain too fine-grained. For example, the
  first ge cells from `Sc` reach only:

  ```text
  c = 1:   Sc + 49
  c = 6:   Sc + 66
  c = 159: Sc + 72
  ```

- A 12-cell walk at `c = 1` advances by about `56` mantissas per cell on the
  ge side. The lt lower-edge walk advances by about `39` or `40` mantissas per
  cell.

Conclusion:

- The mixed predicate is the right soundness interface for small hard cells.
- It cannot be used as a naive global interval walk; the number of cells would
  be determined by the integer-floor bucket width.

I also tried the full mixed-branch interval walk for selected buckets. The
probe ran for more than 90 seconds without producing a completed certificate,
so I interrupted that specific worker with `Ctrl-C`. A first-cell reach probe
then showed why the full walk is not the right global primitive:

```text
ge c=1:   Sc .. Sc+49
ge c=74:  Sc .. Sc+18
ge c=98:  Sc .. Sc+18
ge c=122: Sc .. Sc+18
lt c=1:   MLO .. MLO+63
lt c=6:   MLO .. MLO+35
lt c=143: MLO .. MLO+26
```

At the first ge cell for `c = 1`, the successful branch was the exact direct
top cell:

```text
geResidueRunCellOkB = false
geTopBudgetCoarseCellOkB = false
directTopCellOkB = true
gePhaseCellOkB = false
directResidueCellOkB && gePhaseGapCellOkB = false
```

This confirms that the mixed cell checker is sound and useful locally, but
still far too narrow for a full-domain walk over the positive-shift branch.

## Technique: Pointwise Direct Predicate

The exact direct predicate is:

```lean
posShiftTopDirectOkB m c
```

which checks:

```lean
sumGEB 320 (lnErrArg (toInt (lnTail (evmSub 160 c) m))) lnErrQ
  (posTopX c m) (10^18)
```

This is the cleanest positive-shift witness: if it is available for a point,
the upper cut follows directly through `pos_shift_direct_exact_of_sumGE`.

Result:

- Representative pointwise checks all succeeded, including lower edges,
  upper edges, midpoints, and the known hard witness.
- All-`c` checks at the four representative mantissas also succeeded:

  ```lean
  (List.range 159).all (fun i => posShiftTopDirectOkB Sc (i+1)) = true
  (List.range 159).all (fun i => posShiftTopDirectOkB MLO (i+1)) = true
  (List.range 159).all (fun i => posShiftTopDirectOkB (MHI-1) (i+1)) = true
  (List.range 159).all (fun i => posShiftTopDirectOkB (Sc-1) (i+1)) = true
  ```

- The interval version that freezes `lnErrArg` at the left endpoint remains
  short. This means the pointwise theorem is likely true over the full domain,
  but a monotone-left-endpoint interval proof is too lossy.
- Structured pointwise samples over both branches also succeeded: lower edge,
  lower edge plus small offsets, midpoint, upper edge minus small offsets, and
  the known hard mantissa all passed `posShiftTopDirectOkB` for every
  positive shift bucket checked.
- At the known hard mantissa, the direct residue gap fails only at `c = 6`,
  while `posShiftTopDirectOkB` still succeeds for every `c`.

Conclusion:

- The most promising final route is to prove a correlated direct-staircase
  certificate: `lnTail` and `posTopX` must vary together inside the cell.
- Proving only residue cells, phase cells, or left-frozen direct cells will
  require too many bucket-local intervals.

I also checked the smooth phase-direct pointwise predicate:

```lean
posShiftGePhaseDirectOkB
posShiftLtPhaseDirectOkB
```

Result:

- At the ge lower and upper branch endpoints, every positive-shift bucket
  passes `posShiftGePhaseDirectOkB`.
- At the lt lower and upper branch endpoints, every positive-shift bucket
  passes `posShiftLtPhaseDirectOkB`.
- At `lnErrorHardMantissa`, the lt phase-direct predicate fails for buckets
  `1..151`, while the branch certificate still passes via the hard
  direct-residue route.
- Additional fixed ge samples inside the tightened smooth-envelope failure
  bands all passed `posShiftGePhaseDirectOkB` for every positive-shift bucket.
  This is evidence that the exact integer `x1W` staircase is doing useful work
  even where the smooth polynomial lower envelope is too weak.

Conclusion:

- The current final split is mathematically reasonable: smooth phase direct
  should cover the branches except for the known hard lt mantissa, and the hard
  mantissa is handled by `hardMantissaLtGapBranch_all`.
- The implementation problem is the proof engine for the smooth phase-direct
  statement. The endpoint-freezing phase-cover walker is not an acceptable
  global proof.

## Technique: Slope-Aware Phase Cells

The old phase/direct cells are lossy because they use the phase argument at
the left endpoint and the target at the right endpoint. A more faithful cell
would prove a lower slope for the integer `x1W (zWord m)` term and certify the
phase/direct inequality over a whole interval with that correlated movement.

Lean-only fixed-point diagnostics for the one-step increment

```lean
toInt (x1W (zWord (m + 1))) - toInt (x1W (zWord m))
```

gave:

```text
MLO:                 16
MLO + 10^6:          15
MLO + 10^12:         16
MLO + 10^18:         16
MLO + 10^24:         17
lt midpoint:         13
Sc:                  11
Sc + 10^6:           11
Sc + 10^12:          12
Sc + 10^18:          11
Sc + 10^24:          12
ge midpoint:          9
MHI - 2:              7
```

Result:

- A modest positive slope bound appears mathematically plausible.
- The existing proof stack does not expose such a lemma. `StepMono` and
  `ZOctave` prove qualitative antitonicity/monotonicity by chaining one-step
  inequalities, but they do not quantify a minimum increment.
- A slope-aware cell would need a new formal theorem, probably another
  Kronecker-backed one-step certificate over the generated `x1W` rational
  pipeline.
- I also tested a hypothetical linear-slope cell that assumes
  `x1W (m') - x1W lo >= s * (m' - lo)` and then checks the phase-direct
  inequality with that extra argument at the right endpoint. The first-cell
  reach from the lower edge is:

  ```text
  ge c=1 slope 1..10:   20, 22, 25, 28, 33, 39, 48, 63, 90, 159
  ge c=1 slope 11+:     whole ge branch under the hypothetical assumption

  lt c=1 slope 1..14:   27, 29, 31, 34, 37, 41, 45, 51, 58, 68, 82, 102, 137, 205
  lt c=1 slope 15+:     whole lt branch under the hypothetical assumption
  ```

  This does not prove anything by itself. The actual ge average slope from
  `Sc` to `MHI - 1` is only `9`, and the last ge unit step is `7`; the actual
  lt average slope from `MLO` to `Sc - 1` is `13`. Therefore a single uniform
  branch-wide slope strong enough to close the proof is false.

Conclusion:

- This is a plausible way to replace the frozen-left phase walk.
- It is a substantial new proof component, not just a runtime tweak.
- Any valid version must be interval-specific or use a curved lower envelope
  for `x1W`, probably checked by Kronecker, rather than a global constant
  slope.

## Technique: Formal `x1W` Rational Brackets

The existing floor proof already contains direct rational polynomial brackets
for the generated `x1W (zWord m)` pipeline value:

```lean
bracket_ge_up
bracket_ge_lo
bracket_lt_up
bracket_lt_lo
```

For the ge branch, away from the 46-wide center window:

```lean
evalPoly geTN2b (m : Int) * 2^99 <=
  toInt (x1W (zWord m)) * evalPoly geTD2b (m : Int)
```

For the lt branch, away from the corresponding center window:

```lean
evalPoly ltTN2b (m : Int) * 2^99 <=
  -toInt (x1W (zWord m)) * evalPoly ltTD2b (m : Int)
```

These are already consumed by `FloorCaps` to build the existing cap
theorems, but they can also be used as the formal source of a curved lower
envelope for the phase term. This is stronger than a sampled slope argument:
the certificate would reduce to polynomial nonnegativity obligations over
`m`, replayed by the same `checkCoverK` Kronecker machinery used by the
floor caps.

Result:

- This route remains Lean-only and stays tied to the generated model.
- It avoids trusting any Python-derived slope or smooth-envelope claim.
- It also avoids the unsound endpoint shortcut of checking a larger
  right-endpoint phase argument for every point in an interval.
- The center windows need separate finite handling through the existing
  `FloorWindow` facts or direct point certificates.

Conclusion:

- This is the current best route for a compact global certificate.
- The next proof component should be a correlated direct/phase certificate
  whose boolean checker reduces the whole interval inequality to polynomial
  nonnegativity using these `x1W` brackets, rather than freezing `phase(lo)`
  and `posTopX(hi)` independently.

I added the supporting exact-denominator transfer lemma:

```lean
sumGE_arg_mono
```

This preserves the same Taylor witness length while moving from a certified
lower rational argument `p' / q'` to the target argument `p / q` under the
standard cross-multiplication condition:

```lean
p' * q <= p * q'
```

Result:

- `lake build LnProof.ErrorBoundCore` succeeds cleanly after adding the lemma.
- This is the bridge needed for a Kronecker-checked polynomial certificate:
  the certificate can prove the direct/phase inequality for a rational lower
  envelope with denominator `q' = lnErrQ * TD(m)`, then transfer it to the
  actual integer phase argument at denominator `lnErrQ` without changing the
  required `320` witness.

I also added the generic polynomial margin helper:

```lean
expMarginPoly
sumGE_of_expMarginPoly
ge_phase_lower_algebra
```

and the ge-side envelope definitions:

```lean
posTopXPoly
gePhaseLowerPN
gePhaseLowerQD
gePhaseLowerMarginPoly
```

`gePhaseLowerPN / gePhaseLowerQD` encode the rational lower envelope for the
ge phase argument obtained from `bracket_ge_lo`; `gePhaseLowerMarginPoly` is
the 320-term direct margin that a Kronecker cell certificate should prove
nonnegative.

Result:

- `lake build LnProof.ErrorBoundCore` succeeds after adding these definitions
  and the `posTopXPoly` evaluation theorem.
- The remaining ge-side proof step is to connect `bracket_ge_lo` to the
  cross-multiplication premise of `sumGE_arg_mono`.
- A first direct proof of that cross-multiplication lemma triggered a stack
  overflow during normalization of the polynomial/cast expression. I backed
  out that theorem only, leaving the buildable helper lemmas and envelope
  definitions in place. The next attempt should factor the proof through
  smaller named algebraic atoms before unfolding `posPhaseNatGe`.
- The pure atom-level algebra for that refactor is now checked separately as
  `ge_phase_lower_algebra`. A second attempt that used it avoided the first
  expensive commutative normalization but still overflowed when normalizing
  the casted `posPhaseNatGe` expression. That theorem was also backed out so
  `LnProof.ErrorBoundCore` remains buildable.
- The normalization issue was resolved by proving a separate cast
  decomposition:

  ```lean
  posPhaseNatGe_cast_decomp
  ```

  and then reintroducing the ge lower-envelope theorem without unfolding the
  phase definition in place:

  ```lean
  gePhaseLowerPN_le_phase_mul_TD
  gePhaseLowerMargin_sound
  ```

  `gePhaseLowerMargin_sound` is now the key soundness bridge: any Lean-checked
  proof of `0 <= evalPoly (gePhaseLowerMarginPoly c) m` over an outer ge cell
  produces `PosShiftGePhaseDirectOk 320 m c`.

  Result: `lake build LnProof.ErrorBoundCore` succeeds with this bridge.

I then added the corresponding lt-side lower-envelope bridge:

```lean
ltPhaseLowerPN
ltPhaseLowerQD
ltPhaseLowerMarginPoly
lt_phase_lower_algebra
posPhaseNatLt_cast_decomp
ltPhaseLowerPN_le_phase_mul_TD
ltPhaseLowerMargin_sound
```

The lt numerator is a subtraction. Unlike the ge numerator, it is not
automatically nonnegative from the outer interval hypotheses alone, so
`ltPhaseLowerMargin_sound` explicitly requires a checked proof of:

```lean
0 <= evalPoly (ltPhaseLowerPN c) (m : Int)
```

alongside the checked margin proof:

```lean
0 <= evalPoly (ltPhaseLowerMarginPoly c) (m : Int)
```

Result:

- The lt bridge checks in `LnProof.ErrorBoundCore`.
- The soundness theorem is now available for a finite Lean certificate:
  a table cell can prove both lt numerator nonnegativity and lt direct margin
  nonnegativity, then obtain `PosShiftLtPhaseDirectOk 320 m c`.
- This is still only the semantic bridge. The table data and final public
  theorem wiring are not complete.

I also added reusable lower-envelope cell predicates:

```lean
GePhaseLowerCell
LtPhaseLowerCell
gePhaseLowerCellOkB
ltPhaseLowerCellOkB
gePhaseLowerCellListCoverB
ltPhaseLowerCellListCoverB
gePhaseLowerCell_sound
ltPhaseLowerCell_sound
gePhaseLowerCellListCoverB_sound
ltPhaseLowerCellListCoverB_sound
```

These predicates use `checkCoverK` to replay polynomial nonnegativity over a
cell. The lt cell checks both `ltPhaseLowerPN c` and
`ltPhaseLowerMarginPoly c`; the ge cell checks `gePhaseLowerMarginPoly c`.

Result:

- `lake build LnProof.ErrorBoundCore` succeeds with the new cell machinery.
- A non-cached successful build of the core module during this work completed
  in about `38s`:

  ```text
  lake build LnProof.ErrorBoundCore
  Build completed successfully (93 jobs).
  ```

- The cell predicates are sound, but they are not yet the final certificate
  representation. A Lean `#eval` probe of a single ge lower-envelope cell
  using the live definition of `gePhaseLowerMarginPoly` produced no result
  before manual interruption after roughly two minutes. A metadata probe of
  the live `expMarginPoly 320`-based definitions also produced no result
  before manual interruption after roughly one minute.

Conclusion:

- The semantic correlated-envelope bridge is now present for both positive
  branches.
- The remaining proof-engineering problem is representation: the final
  certificate should not ask the kernel to construct
  `expMarginPoly 320 ...` live inside every table check.
- The likely next step is to materialize phase-lower margin literals, or to
  introduce a specialized checked representation whose small boolean predicate
  does not rebuild the source degree-320 polynomial during reduction.

I then replaced the lower-envelope margin polynomial builder with a direct
recurrence:

```lean
expMarginFastState
expMarginPolyFast
evalPoly_expMarginPolyFast
sumGE_of_expMarginPolyFast
```

The recurrence constructs the same semantic margin without recomputing powers:

```text
M_0       = w - y
P_0       = 1
P_{n+1}   = PN * P_n
M_{n+1}   = (n + 1) * QD * M_n + w * P_{n+1}
```

This avoids the old `expPolyNum`/`polyPow` builder shape in the
lower-envelope definitions:

```lean
gePhaseLowerMarginPoly
ltPhaseLowerMarginPoly
```

Result:

- `lake build LnProof.ErrorBoundCore` succeeds cleanly with the recurrence.
- The recurrence is semantically checked by Lean; the bridge to `sumGE` does
  not trust a generated literal.
- This is a useful local improvement, but it does not by itself make live
  degree-320 source-polynomial construction suitable for global table checks.
  A metadata probe:

  ```lean
  #eval (gePhaseLowerMarginPoly 1).length
  ```

  still produced no output after about one minute and was manually
  interrupted.

Conclusion:

- Keep the recurrence. It removes a clearly wasteful polynomial-construction
  path and gives a cleaner semantic bridge.
- Do not rely on live `gePhaseLowerMarginPoly`/`ltPhaseLowerMarginPoly`
  construction in the final public theorem dependency. Materialized literals
  or a smaller replay object are still needed.
- The low-degree inputs have length `13`, so the direct degree-320 margin has
  degree about `1 + 12 * 320 = 3841`. This is far outside the scale for the
  existing floor-proof `checkCoverK kB` source guard. A raw source-polynomial
  check would need an `aeval` budget at roughly `lo^3841`, so `kB = 38000` is
  structurally the wrong scale even if the polynomial list were materialized.

I also tested a sound interval-replay representation that avoids constructing
the degree-320 margin polynomial at all:

```lean
expMarginVal
expMarginIvState
expMarginIvLower
expMarginIvLower_sound
polyIvOnCell
gePhaseLowerIvCellOkB
ltPhaseLowerIvCellOkB
```

This checker bounds the scalar recurrence from interval bounds on the
low-degree `PN`, `QD`, and `posTopX` polynomials. It is Lean-checked, fast to
evaluate, and avoids `native_decide`.

Result:

```lean
#eval gePhaseLowerIvCellOkB (Sc + 46) (Sc + 46) 1  -- true
#eval gePhaseLowerIvCellOkB (Sc + 46) (Sc + 1000) 1 -- false
#eval ltPhaseLowerIvCellOkB MLO (MLO + 1000) 1 -- false
```

First-cell reach probes with `phaseSearchMax 128` returned only the left
endpoint for both `c = 1` and `c = 159` on both ge and lt sides.

Conclusion:

- The interval-replay idea is fast but too conservative in its independent
  interval form.
- Do not wire this checker into the public branch certificate as-is.
- A useful interval variant would need stronger correlation, for example a
  shifted polynomial/literal for the whole recurrence or a Taylor-model style
  remainder bound, not independent intervals for `PN`, `QD`, and the running
  margin.

I also checked the exact direct margin:

```lean
directMargin m c =
  expSumState (lnErrArg (toInt (lnTail (evmSub 160 c) m))) lnErrQ 320
```

with the comparison rearranged as:

```lean
(exp numerator) * 10^18 - posTopX c m * (exp denominator)
```

Result:

- The margin was nonnegative at all sampled points.
- Adjacent margins are not monotone. They usually drift downward inside an
  output bucket and jump when `lnTail` increments.

Conclusion:

- The direct predicate is the right semantic shape, but a final proof cannot
  be a single endpoint or threshold argument.
- A viable direct certificate needs to encode the staircase jumps or prove a
  lower envelope that already accounts for them.

## Technique: Reusing `df29feae`

I inspected the other agent's commit `df29feae`.

What it proves:

- A weaker `1.7035` ulp bound.

The main shortcut there:

```lean
lnErrorCoarsePosResidue = 0
```

This permits:

```lean
PosShiftResidueOk_uniform
```

which proves the positive-shift residue predicate for every point from the
basic floor-bracket positivity of `posResidueGap`.

Result for the exact bound:

- This shortcut is not applicable.
- In the exact-bound tree, `lnErrorCoarsePosResidue` is positive:

  ```lean
  11562080766880751500032140603279015936
  ```

- `df29feae` also changes generated/formal constants such as `BIASc`,
  `FloorCertDefs.EUN`, and floor cap constants. Those are not applicable here
  because the proof must remain tied to the current generated model.

Transferable idea:

- Split the proof into a broad residue route and a small direct hard route.

Non-transferable idea:

- The uniform positive-residue theorem.

Conclusion: use the decomposition pattern, not the constants or the zero
residue shortcut.

## Technique: First-Order Budget Instead Of 320-Term Sum

I checked whether the phase/direct branch could be replaced by existing cap
algebra plus a first-order cap for the extra fractional ulp.

Diagnostic predicates:

```lean
phaseBudgetGeB
phaseBudgetLtB
phaseGapBudgetGeB
phaseGapBudgetLtB
```

Result:

- The plain phase budget was false at representative points.
- The direct-gap phase budget was also false at representative points.
- A direct-gap exponential cap buys only about `6886` or `6887` in the
  `10^-31` budget scale.
- The existing positive coarse budget needs `7068`.

Conclusion: the first-order budget route is too weak. The exact proof must
use non-simultaneity of the staircase and phase terms, not only a larger
constant cap.

## Technique: Higher-Order Residual Top Budget

The pointwise top-budget branch uses the actual leftover argument:

```lean
posAvailGe m c (toInt (lnTail (evmSub 160 c) m))
```

The existing proof consumes that argument with the first-order lower cap
`e^a >= 1 + a`. I tested replacing this local residual cap by higher-order
partial sums while keeping the same factored `x1`, `ln2`, and bias caps.

Result:

- Degree `2`, `3`, `4`, `5`, `8`, `12`, `16`, `24`, `32`, `48`, and `64`
  residual caps still miss the same ge lower-edge modular cases.
- The misses are not caused by truncating the residual exponential.
- The stronger `capBiasL3403` and exact `10^18` denominator also do not close
  these cases.

Representative ge misses for the coarse-residue-or-top-budget split:

```text
c = 74:  offsets from Sc include 0, 56, 112, 168, 224
c = 98:  offsets from Sc include 0, 56, 112, 168, 224, 280
c = 122: offsets from Sc include 0, 56, 112, 168, 224, 280
```

At offset `280`, `c = 74` is already covered again, while `c = 98` and
`c = 122` still miss. Samples at `Sc + 10^6`, `Sc + 10^12`, mid-octave, and
near `MHI - 1` are covered by both coarse residue and top budget.

Conclusion:

- Increasing only the residual Taylor degree is the wrong lever.
- These are true floor-bucket alignment pockets. A final compact certificate
  has to encode those pockets directly or prove a modular lower envelope for
  them.

## Technique: Refined Ge-Side Coarse Budget

The existing positive coarse budget uses a global mantissa lower bound
`m >= 2^95`. For the ge branch, we know the stronger fact `m >= Sc`.

I checked the required budget cap under this stronger ge-side lower bound.

Result:

```text
global positive budget cap needed: 7068
ge-side budget cap with m >= Sc: 6994
```

This was computed by the diagnostic:

```lean
errBudgetLGeCap
firstCapFrom
```

The result was uniform over all positive-shift `k` values checked.

Conclusion:

- This is a real improvement for the ge branch.
- It is still not enough for the exact `1.688558253` bound.
- It may shrink the finite hard set or simplify the ge branch, but it does not
  eliminate the need for a residue/direct certificate.

## Technique: Ge-Specific Coarse Residue Constants

The ge-side budget improvement gives a smaller cap, so I computed the exact
coarse residue needed for that cap:

```lean
lnErrorCoarseGePosBudgetCap := 6994
lnErrorCoarseGePosResidue :=
  6871773546036302714494338743387815936
```

The corresponding threshold is:

```text
ceil(lnErrorCoarseGePosResidue / (2^27 * 10^9))
  = 51198702648552527387
```

This is lower than the existing positive residue threshold:

```text
86144214621787901969
```

I added and checked the core certificate facts:

```lean
capECoarseGePosL
errBudgetLGe_all
errBudgetLGe_le
```

Result:

- `LnProof/ErrorBoundCert.lean` checked successfully after adding these facts.
- This gives a viable ge-only residue route.
- It does not automatically solve the lt branch, and it does not by itself
  prove the public theorem.

Conclusion:

- Keep the ge-specific cap path.
- Refactor or duplicate the positive exact-cap theorem so the ge branch can
  consume `lnErrorCoarseGePosResidue` instead of the larger global positive
  residue.

## Technique: Stronger Uniform Lower-Cap Experiment

I checked whether the existing cap certificates could be tightened by using a
stronger uniform lower bound for the transformed exponential input. The goal
was to lower the positive budget enough that the residue route would cover
more or all of the positive-shift domain.

Result:

```text
first ge floor cell with cap 3400: false
first ge floor cell with cap 3401: true
later checked cell with cap 3400: true
```

The first ge cell is the blocker. Later cells have enough slack, but the
uniform cap must hold for every cell if it is going to replace the current
global constant.

Conclusion:

- A uniform stronger lower cap is not available in the current cell layout.
- A local refinement near the first ge cell may still be useful, but it is not
  a drop-in replacement for the existing cap algebra.

## Technique: Direct Residue Gap

The exact theorem needs to exploit the truncated integer staircase. The
relevant quantity is:

```lean
posResidueGap m c r =
  (r + 1) * 2^72 - posAccI m c
```

The coarse predicate requires:

```lean
posResidueGapThreshold <= posResidueGap m c r
```

where:

```lean
posResidueGapThreshold = 86144214621787901969
```

The direct hard branch needs only:

```lean
lnErrorDirectResidueGap <= posResidueGap m c r
```

where:

```lean
lnErrorDirectResidueGap = 336460000000000000
```

Result:

- The known hard witness fails the coarse residue predicate.
- The known hard witness passes the direct residue predicate.
- This matches the intended "integer staircase" explanation: the maximal
  smooth error components do not occur together with the worst bucket-edge
  residue.

Conclusion:

- A final proof should certify that every positive-shift point either has the
  coarse residue gap or belongs to a replayable finite direct-gap/phase
  certificate.
- This is the real missing proof obligation.

## Technique: Modular Residue Exclusion

I added a small Lean-checked congruence helper to `LnProof.ErrorBoundCore`:

```lean
firstCongruentGE
firstCongruentGE_le_of_mod
no_congruent_of_first_gt
bucket_index_eq_of_mod_bracket
```

It proves that if the first integer `>= lo` congruent to `r mod q` is already
past `hi`, then no point in `[lo, hi]` has that residue. This is the basic
kernel-checkable ingredient for a replayable residue-exclusion certificate.
The bucket-index lemma proves uniqueness of the integer floor bucket from an
abstract `d * q + rem` decomposition, which is the companion fact needed to
turn accumulator modulo information back into `lnTail` bucket information.

Result:

- The helper checks without `native_decide`.
- `lake build LnProof.ErrorBoundCore` succeeds after adding these lemmas.
- This does not yet solve the public theorem. It only provides the arithmetic
  backbone for excluding impossible high-residue accumulator cases once a
  cell has an affine residue model.
- A direct `posResidueGap = 2^72 - (posAccI mod 2^72)` probe still needs a
  careful rewrite path. The abstract bucket lemma checks, but the first
  concrete identity attempt triggered a stack overflow while rewriting the
  large unfolded terms.

Conclusion:

- Use this as a building block for direct-witness cells that exclude the bad
  top-of-bucket residues.
- The next required proof step is connecting accumulator residues in a cell to
  congruence classes that this helper can exclude.

## Technique: Constant-Tail Residue Cells

I added a Lean-side residue-cell checker for the ge branch:

```lean
geResidueCellOkB lo hi c
geResidueCellOkB_sound
```

The checker proves an interval sound if:

- `Sc <= lo`
- `lo <= hi`
- `hi < MHI`
- `c < 160`
- the endpoint `lnTail` values are equal
- the right endpoint satisfies `geResidueGapOkB`

The supporting lemmas are:

```lean
posAccI_mono_m
lnTail_eq_of_same_posAcc_endpoints
posResidueGap_ge_of_same_posAcc_endpoints
```

Result:

- The new lemmas check with the same existing axiom footprint as the rest of
  the proof (`propext`, `Classical.choice`, `Quot.sound`).
- This gives a sound way to replay constant-staircase cells.
- It does not by itself solve the global proof, because constant-tail cells
  are expected to be short near the hard bucket-boundary regions.

Conclusion:

- Keep this checker as a building block for a direct-witness certificate.
- It should be combined with broader phase/top-budget cells or a Kronecker
  interval certificate; using it alone would likely require too many cells.

## Technique: Residue-Run Cells

I added a sharper residue interval predicate:

```lean
geResidueRunCellOkB
residueRunCellOkB
```

and soundness lemmas:

```lean
geResidueRunCellOkB_sound
residueRunCellOkB_sound
```

Unlike `geResidueCellOkB`, these cells do not check endpoint `lnTail`
equality. They prove all points stay below the left endpoint's next
`2^72` accumulator boundary and above the required residue threshold:

```lean
posAccI hi c < (rlo + 1) * twoPow72I
threshold <= ((rlo + 1) * twoPow72I - posAccI hi c) * 2^27 * den
```

The tail equality for interior points is then proved from the floor bracket
and monotonicity of `posAccI`, using `Int.mul_lt_mul_right` to cancel the
positive `2^72` factor.

Result:

- The soundness lemmas check with the normal imported axiom footprint.
- The lt branch certificate was extended to accept the existing
  `PosShiftResidueOk` route, so lt cells can now use residue witnesses before
  falling back to top-budget/phase/direct-gap.
- Representative mixed-branch interval reach from the lower edges is still
  small:

  ```text
  ge c=1:   Sc .. Sc+30
  ge c=159: Sc .. Sc+52
  lt c=1:   MLO .. MLO+37
  lt c=159: MLO .. MLO+26
  ```

Conclusion:

- This is a cleaner and slightly stronger residue-cell primitive.
- It still does not solve the global proof because bucket-local residue
  intervals are intrinsically short near the hard edge.

I then added the concrete bridge from the EVM accumulator bucket to modular
residue arithmetic:

```lean
twoPow72N
posResidueGap_eq_twoPow72_sub_mod
directResidueGapModOkB
PosShiftDirectResidueGapOk.of_modB
```

This proves, for the positive-shift floor bucket,

```lean
posResidueGap m c r =
  (2^72 - (posAccI m c).toNat % 2^72)
```

with the usual `2^72` value interpreted as an `Int` on the left. This is the
missing local bridge needed before a modular exclusion certificate can talk
about accumulator residues instead of re-evaluating `lnTail`.

I also added a direct-residue run cell:

```lean
directResidueRunCellOkB
directResidueRunCellOkB_sound
```

and wired it into the mixed branch-cell checker before the older endpoint
equality direct-residue cell.

Result:

- `lake build LnProof.ErrorBoundCore` succeeds after the additions.
- The new theorem axiom footprints are exactly:

  ```text
  [propext, Classical.choice, Quot.sound]
  ```

- Lower-edge reach diagnostics were unchanged:

  ```text
  ge c=1:   Sc .. Sc+49
  ge c=74:  Sc .. Sc+18
  ge c=98:  Sc .. Sc+18
  ge c=122: Sc .. Sc+18
  lt c=1:   MLO .. MLO+63
  lt c=6:   MLO .. MLO+35
  lt c=143: MLO .. MLO+26
  ```

- Direct run-cell checks over `+1000` lower-edge intervals for representative
  hard buckets were false, so this primitive is a proof-enabling bridge rather
  than the missing global certificate by itself.

Conclusion:

- Keep the modular bridge; it is necessary for any replayable modular
  exclusion certificate.
- Do not expect direct run-cells alone to improve runtime or cover size near
  the lower hard edge.

## Technique: Hard Witness Locality

The known exact-bound witness is:

```text
x = 908208608734269882705518908582724367050947602720364149283237552328122826751
evmClz x = 6
m = 39770979022059719714796403827
r = 131151069119194409175516583694
```

At this point:

```text
residueGapOkB = false
directResidueGapOkB = true
posShiftLtBranchCertB = true
```

I also checked a small neighborhood around the hard mantissa for `c = 6`.
The exact hard mantissa is the only point in that local window where
`PosShiftLtPhaseDirectOk 320` failed; nearby points passed the branch
certificate.

Result:

- The exact hard point is already covered by `hardMantissaLtGapBranch_all`.
- The hard witness behavior supports the direct-witness certificate shape.
- It does not justify a smooth envelope proof, because the failure and success
  are controlled by integer bucket alignment.

Conclusion:

- The final certificate should have explicit hard-point or hard-cell records.
- It should not try to erase the staircase with a monotone real envelope.

## Technique: Kronecker-Shifted Polynomial Certificates

The repository already has a strong finite-certificate pattern:

```lean
LnProof.KroneckerShift.checkCoverK
LnProof.KroneckerShift.checkCoverK_sound
```

This is used by the floor proofs, for example:

```lean
FloorCertGeLo
FloorCertGeUp
FloorCertLtLo
FloorCertLtUp
```

The pattern:

1. Represent the inequality as a polynomial nonnegativity claim.
2. Taylor-shift at each cell's left endpoint.
3. Use Kronecker substitution to compute shifted coefficients efficiently.
4. Prove the shifted polynomial literal is extensionally equal to the original
   polynomial at `2^kB`.
5. Use interval Horner on the shifted cell.

Result:

- This technique is already proven and CI-shaped in the repo.
- It is likely the right replacement for the hanging phase-cover booleans.
- Directly building a degree-320 exponential polynomial may be too large, so
  the certificate should probably use the existing cap-factor algebra where
  possible and reserve high-degree checks for small hard cells.
- A one-shot shifted Kronecker equality check is not automatically viable for
  the phase-lower margin cells. For the representative ge outer cell
  `lo = Sc + 46`, `c = 1`, the shifted source/literal absolute-evaluation
  guard needs roughly `2^592238`, while the existing `kB` is `38000`. Raising
  the substitution base enough would create enormous integers for a
  degree-3841 equality check, so the current `shiftedExpMarginCellOkB` shape is
  better treated as an experimental bridge than as the final replay primitive.

Conclusion:

- Use Kronecker for finite cell certificates.
- Avoid asking the kernel to reduce `sumGEB 320` globally.
- Prefer low-degree or factored inequalities over raw `expPolyNum 320`.
- If a degree-320 check remains necessary, materialize the polynomial literals
  or a smaller replay object. The current live
  `expMarginPoly 320 ...` construction is too expensive to use directly in
  global table checks.
- For phase-lower outer cells, investigate modular coefficient replay,
  coefficient chunks, or factorized interval witnesses instead of a single
  full-polynomial Kronecker substitution at a huge base.

## Technique: Tightened `x1` Caps For The Exact Fractional Route

I checked whether the positive-shift proof can avoid the phase/direct global
certificate entirely by tightening the existing `x1` caps and using only the
published fractional extra cap:

```lean
lnErrorExtraCap = 6885
capBiasL3403
```

The required budget checks close with:

```text
ge branch: x1 lower slop 3292, bias slop 3403
lt/full positive branch: x1 cap slop 3218, bias slop 3403
```

The corresponding Lean diagnostics were:

```lean
(List.range 160).all (errBudgetLGeFracTight 3292 3403) = true
(List.range 160).all (errBudgetLFracTight 3218 3403) = true
```

Near the `Sc` window, the pointwise checks also support these tighter caps:

```lean
(List.range 46).all (wCheckGeLoSlop 3292) = true
(List.range 45).all (wCheckLtUbSlop 3218) = true
```

This initially made the route look mathematically plausible, but it is not a
completed proof. The existing wide Kronecker cells were tuned for `3401`; under
the tighter constants they do not replay unchanged:

```text
ge existing cells under 3292: all old cells fail
lt existing cells under 3218: some old cells pass, several fail
```

Materializing the two tightened polynomial literals from Lean evaluation gives
about `3.3 MB` of list literals. The lists type-check, and cell checks against
them stay low-memory, but cell witness generation still needs to be completed.

For ge, a uniform `1e27` cell walk over the outside-window range has 24 cells
and fails only at selected cells. Splitting failed cells iteratively gave:

```text
24-cell 1e27 walk: fails at 7 cells
31-cell first split: fails at 8 cells
39-cell second split: fails at 9 cells
```

After materializing the tightened floor certificate literal, direct evaluation
showed that the ge-side smooth envelope itself fails at sampled in-domain
points:

```lean
#eval decide (0 ≤ evalPoly certGeLo3292Lit
  (63022770974786139918731938273 : Int)) -- true
#eval decide (0 ≤ evalPoly certGeLo3292Lit
  (63072770974786139918731938273 : Int)) -- false
#eval decide (0 ≤ evalPoly certGeLo3292Lit
  (63122770974786139918731938272 : Int)) -- false
#eval decide (0 ≤ evalPoly certGeLo3292Lit
  (63222770974786139918731938272 : Int)) -- true
```

That rejects this route as a global smooth-envelope proof. It also matches the
mathematical shape of the exact bound: the `1.688558253` ulp result is not a
smooth cap over the real-valued error envelope. It relies on the truncated
integer staircase and the fact that the separate sources of error do not reach
their maxima simultaneously.

I then checked whether the tightened ge literal can still be useful as a
partial certificate. A 24-cell `1e27` Kronecker walk over the ge branch gave:

```text
passing coarse cells:
  0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 14, 15, 16, 17, 19, 20

failing coarse cells:
  6, 7, 13, 18, 21, 22, 23
```

Subdividing the failing coarse cells into `1e26` cells localized the failures
to these bands:

```text
[62922770974786139918731938227, 63222770974786139918731938226]
[69122770974786139918731938227, 69522770974786139918731938226]
[74322770974786139918731938227, 74722770974786139918731938226]
[77822770974786139918731938227, 78122770974786139918731938226]
[79222770974786139918731938227, 2^96 - 1]
```

The corresponding `H(m) = toInt (x1W (zWord m))` endpoint ranges are:

```text
73618735233434291613860976345 .. 76633474328918415907147689680
133183162583092409021708309621 .. 136840414304380646270483691059
179156517758532671038769770189 .. 182558574947413168511149665397
208323064053825743948382186202 .. 210761707983292245946785092637
219623976087343528007162558130 .. 219667109870829893404565884302
```

Those bands are much smaller than the whole branch, but they are still wide
enough to contain many accumulator-residue periods. A simple "tight smooth cap
outside, residue inside" proof would still need a modular/staircase argument
inside the bands.

Conclusion:

- Do not use the tightened smooth floor-cap route as the final proof.
- The tightened cap can be a useful pruning certificate for most of the ge
  branch.
- The exact proof still needs a correlated staircase/direct certificate for
  the remaining bands, not just a stronger uniform smooth cap.

Follow-up Lean-only probes against the materialized tight literals confirmed
the practical shape of this route.

The old first wide ge cell under the tight literal did not return a boolean
promptly when reduced directly through `checkCoverK`. That is a poor proof
shape because the cell is already known to fail, but Lean still has to perform
the packed shift/evaluation-identity work before it can return `false`.

Successful narrow checks reduce quickly:

```lean
checkCoverK kB certGeLo3292Lit
  56022770974786139918731938273
  56022770974786139918731939273
  [1000] = true

checkCoverK kB certLtLo3218Lit
  39614081257132168796771975168
  39614081257132168796771976168
  [1000] = true
```

Larger local checks also succeed at the lower endpoints, but not uniformly
across the old coarse cell starts. A conservative `1e26`-style ge sample over
selected old floor-cell starts gave:

```text
56022770974786139918731938273: true
62248863508307989581262617184: true
63042232383408656869457414738: false
64929052012891719377728977368: true
68717504609657537844941640471: true
69643680272268497720544738510: true
73761687789119228727691347874: true
74497159690857676763262189493: false
77437517811705333581000648121: true
78001071025949577278638182917: false
```

This reinforces the current conclusion: if the tight floor literals are used
in the final Lean proof, they should be used as adaptive pruning certificates
over passing regions. The failing regions still need either smaller local
cells or the staircase-aware residue/direct branch machinery. The final proof
should not ask the kernel to reduce known-failing wide `checkCoverK` cells.

## Technique: Reducing Taylor Degree

I checked whether the phase-direct lower sum can use fewer terms than `320`:

```lean
sumGEB n (posPhaseNatGe m c + lnPhaseExtraArg) ...
sumGEB n (posPhaseNatLt m c + lnPhaseExtraArg) ...
```

Result:

- At representative lower-edge points, `n = 22`, `32`, and `64` are false.
- At the same points, `n = 96`, `128`, `160`, `224`, and `256` are false.
- `n = 320` is true at the checked lower-edge ge and lt samples.

Conclusion:

- The existing degree-22 floor-certificate polynomial style cannot be reused
  directly for the phase-direct sum.
- A raw Kronecker certificate over `expPolyNum 320` would likely be too large;
  a practical proof should be factored or use a sharper non-polynomial
  certificate primitive.

## Technique: Exact Factored Budget At Published Extra

I checked the ge-side factored budget with only the published fractional extra
cap `6885`, replacing the coarse ge cap `6994`:

```lean
errBudgetLGeCapB 6885 k
```

Result:

- Every `k` in `0..159` fails with cap `6885`.
- Every `k` in `0..159` succeeds with the current ge coarse cap `6994`.
- The full positive-shift budget similarly fails every `k` with `6885` and
  succeeds with the current `7068`.

Conclusion:

- The factored cap proof is uniformly short of the exact bound; the miss is
  not localized to a few shift buckets.
- Tightening one constant by a unit is not enough. The proof needs either a
  sharper local product certificate or a correlated direct/phase certificate.

## Technique: Monotonicity

Useful monotonicity already exists or has been added:

```lean
r1_mono
tail_mono
lnTail_mono_m
posTopX_mono_m
posPhaseNatGe_mono_m
posPhaseNatLt_mono_m
```

Result:

- These lemmas are enough to make conservative interval cells sound.
- They do not prove the modular residue property.
- The current endpoint-freezing cell predicate loses too much margin because
  it combines the worst exponent endpoint with the worst target endpoint.

I also started checking whether the actual pointwise phase margin has a
one-sided minimum at the branch boundary. The direct pointwise scan was too
slow because each point still evaluates `sumGEB 320`, so I interrupted it.

I later checked deterministic adjacent differences of the actual `320`-term
phase margins near the lower edge:

```lean
gePhaseMarginI (Sc + i + 1) 1 - gePhaseMarginI (Sc + i) 1
ltPhaseMarginI (MLO + i + 1) 1 - ltPhaseMarginI (MLO + i) 1
```

Result:

- The ge adjacent-difference booleans in the first 20 steps are mixed.
- The lt adjacent-difference booleans in the first 20 steps are also mixed.
- The endpoint margins checked there are nonnegative, but the margin is not
  monotone.

Conclusion:

- Monotonicity is useful for soundness once a sharper cell predicate exists.
- It is not, by itself, the final proof.

## Technique: Current JSON/Python Certificate Artifact

There is a JSON artifact at:

```text
formal/python/ln/ln_error_certificate.json
```

Its current shape has:

```text
discarded: 1 record
leaves: 1 record
```

Result:

- It records the known witness and a broad discarded region.
- It is not yet a rigorous replayable global certificate for Lean.
- It should not be trusted as a proof of the theorem.
- Current work should not keep building Python scripts unless explicitly
  requested; the proof work should be in Lean.

Conclusion:

- The JSON is useful as a diagnostic artifact only.
- The final theorem must depend on Lean-checked certificate predicates.

## Rejected Or Currently Unusable Approaches

- `native_decide`: disallowed.
- Process-wide termination commands such as `pkill` or `killall`: disallowed.
- Copying constants from `df29feae`: invalid because they are tied to a
  different generated/formal state.
- Uniform positive-shift residue proof: false for the exact bound because the
  positive coarse residue is nonzero.
- Brute global `decide +kernel` over phase cover: too slow and the current
  cell predicate is too conservative.
- Treat external process termination of a Lean worker as operational noise, not
  proof evidence. The actionable issue is still that the old global phase-cover
  reduction is too expensive and too coarse for CI.
- Replacing the phase branch with only a first-order extra cap: too weak.
- Hand-trusting Python output: not acceptable for the public theorem.

## Most Promising Next Route

The final proof should replace:

```lean
positive_shift_ge_phase_cover_all
positive_shift_lt_phase_cover_all
```

with a finite Lean certificate that proves the positive-shift branch by a
split:

1. Coarse residue succeeds:

   ```lean
   residueGapOkB m c r = true
   ```

   This gives `PosShiftResidueOk` and reuses `lo_ge_pos_exact` or
   `lo_lt_pos_exact`.

2. Coarse residue fails, but the point is covered by a direct witness record:

   ```lean
   directResidueGapOkB m c r = true
   ```

   plus a checked phase/direct cap.

3. The hard direct records should be replayable in Lean by compact literals,
   preferably using `checkCoverK` or a similarly small boolean checker.

The current Lean bridge supports such records for both sides:

```lean
gePhaseLowerMargin_sound
ltPhaseLowerMargin_sound
```

The open engineering decision is how to encode the replay object. Live
construction of the `expMarginPoly 320` source polynomial should be avoided in
the public theorem dependency; the final generated Lean literals should reduce
like the existing floor certificate files, with small per-cell checks.

For the ge side, the `m >= Sc` budget refinement should be kept in mind
because it reduces the required coarse positive cap from `7068` to `6994`.
That may significantly reduce the finite direct set.

For the lt side, the exact hard mantissa:

```lean
lnErrorHardMantissa = 39770979022059719714796403827
```

already has an exact direct branch checker:

```lean
hardMantissaLtGapBranch_all
```

The remaining work is to generalize that from one exact mantissa into a
replayable finite hard-set certificate, without falling back to a global
kernel reduction over `sumGEB 320`.

## Practical Proof Engineering Notes

- Keep `sumGEB` in recurrence form. It is locally faster.
- Do not put large global reductions inside public theorem dependencies.
- Prefer small generated theorem files with explicit checked literals, matching
  the existing floor certificate style.
- If using Kronecker-shifted certificates, keep each cell theorem small, as the
  floor proofs do with `FloorCertGeLoC00`, `FloorCertGeLoC01`, and so on.
- Do not use live `expMarginPoly 320` construction in the final global cover
  theorem; materialize or factor the replay data first.
- Do not use `checkCoverK kB` directly on the raw phase-lower margin source
  polynomial. Its degree is about `3841`, so the source `aeval` guard is the
  wrong shape for this proof. Prefer shifted local replay objects, factored
  low-degree obligations, or another checker whose soundness does not require
  a global source-polynomial absolute-evaluation bound at the mantissa scale.
- Use `#print axioms model_ln_wad_error_bound_1_688558253` after the build to
  confirm that no new axioms have leaked in.

## Current Lean Experiments: Phase Cover Replacement

The old public wrapper still contains:

```lean
positive_shift_ge_phase_cover_all
positive_shift_lt_phase_cover_all
```

Building `LnProof.ErrorBound` with those facts fails quickly with a Lean stack
overflow inside the global `decide +kernel` reduction. This is not a useful
CI proof shape.

Targeted Lean `#eval` probes, without `native_decide`, gave:

- `gePhaseCoverFastB 1024 1 Sc (MHI - 1) = false`
- `ltPhaseCoverFastB 1024 1 MLO (Sc - 1) = false`
- `gePhaseCoverFastB 1024 1 (Sc + 46) (MHI - 1) = false`
- `ltPhaseCoverFastB 1024 1 MLO (Sc - 46) = false`
- A single original-fuel probe for `gePhaseCoverFastB phaseCoverFuel 1 ...`
  produced no result after about two minutes and was interrupted.
- A single dynamic `geBranchCoverB branchCoverFuel 1 ...` probe also produced
  no result after about one minute and was interrupted.

The first smooth ge cell at `c = 1`, `lo = Sc + 46`, reaches only:

```text
56022770974786139918731938291
```

so the smooth phase cover advances by small cells near the center. This
explains why the old global search/reduction is unsuitable.

The central mantissa windows are better handled by small point certificates:

```lean
(List.range 159).all (fun ci =>
  (List.range 45).all (fun i =>
    posShiftLtBranchCertB (Sc - 45 + i) (ci + 1)
      (toInt (lnTail (evmSub 160 (ci + 1)) (Sc - 45 + i)))))
= true

(List.range 159).all (fun ci =>
  (List.range 46).all (fun i =>
    posShiftGeBranchCertB (Sc + i) (ci + 1)
      (toInt (lnTail (evmSub 160 (ci + 1)) (Sc + i)))))
= true
```

These checks are small enough to reduce promptly. The outer regions should be
covered by finite generated phase-lower cell tables:

- ge outer region: `[Sc + 46, MHI - 1]`
- lt outer region: `[MLO, Sc - 46]`, with the exact hard mantissa handled by
  the existing hard-mantissa branch certificate

The Lean-side shifted checker now builds in `LnProof.ErrorBoundCore` and gives
a soundness bridge for local experiments:

```lean
shiftedExpMarginCellOkB
shiftedExpMarginCellOkB_sound
gePhaseLowerMarginVal_sound
ltPhaseLowerMarginVal_sound
```

Current build result:

```text
lake build LnProof.ErrorBoundCore
```

passes. The public theorem still needs the outer finite certificate tables
before `LnProof.ErrorBound` can build without the old global phase-cover facts.
The current one-shot shifted checker is not expected to be the final table
checker for those outer cells unless it is changed to avoid the large
absolute-evaluation guard.

## Current Lean Experiments: Minimum Residual Phase Target

The decomposition of `lnErrArg` includes the fractional extra plus at least
one positive output residual unit:

```lean
minPosAvail = lnPhaseExtraArg + twoPow27N * lnErrorBoundDen
```

The old phase-direct predicates used only `lnPhaseExtraArg`. I added Lean
predicates and model-level soundness lemmas for the stronger target:

```lean
PosShiftGeMinPhaseDirectOk
PosShiftLtMinPhaseDirectOk
model_ln_wad_positive_shift_ge_min_phase_direct
model_ln_wad_positive_shift_lt_min_phase_direct
gePhaseLowerMarginValMin_sound
ltPhaseLowerMarginValMin_sound
```

Current build result:

```text
lake build LnProof.ErrorBoundCore
```

passes with these lemmas.

The new theorem axiom footprints are the normal imported footprint:

```text
[propext, Classical.choice, Quot.sound]
```

Diagnostics:

- `sumGEB 320 (phase + minPosAvail) ...` is true at representative ge
  endpoints (`Sc`, `Sc + 10^24`, and `MHI - 1`) for all checked `c`.
- It is true at representative lt endpoints (`MLO`, `Sc - 1`, and
  `Sc - 10^24`) for all checked `c`.
- It is false at the known hard mantissa:

  ```lean
  lnErrorHardMantissa = 39770979022059719714796403827
  ```

  The existing exact hard-mantissa branch certificate covers that singleton.
- For `c = 1`, a 101-point neighborhood around the hard mantissa showed the
  min-phase predicate failing only at the hard mantissa itself.
- The 320-term partial sum is still needed for this target at representative
  points; attempts with `n = 20, 30, 40, 50, 64, 80, 100, 128, 160, 200,
  256` were false, while `n = 320` was true.

Rejected subroutes for this target:

- Frozen-endpoint cells remain tiny. Even with `minPosAvail`,
  `geMinPhaseCellOkB Sc (Sc + 10) 1` and the analogous lt window checks are
  false.
- Naive interval arithmetic over `p`, `q`, and `y` is still too conservative;
  singleton cells are true, but width-10 cells near `Sc` are false.
- Live construction of `expMarginPolyFast 320 ...` did not return promptly
  even for a single `c` diagnostic, so the final proof still needs a compact
  replay object.

Conclusion:

- The current best certificate target is likely:

  ```text
  ge: min-phase direct over the outer and central ge region
  lt: min-phase direct over the lt region except lnErrorHardMantissa,
      plus the existing hard-mantissa branch
  ```

- This avoids trusting pointwise residue/top-direct behavior and uses the
  already-proved positive residual decomposition.
- It does not remove the need for a correlated certificate checker. The final
  checker still must avoid the old frozen-left cells, naive independent
  intervals, and one-shot huge-base Kronecker equality.

I also checked whether the min-residual target could be converted back into a
low-degree factorized product-cap proof. The existing strict product budget
still needs roughly the ge coarse cap:

```text
cap = 6885, 6886, 6887, 6888, 6890, 6900, 6950: ge budget false
cap = 6994: ge budget true
```

Using the tighter bias cap `capBiasL3403` improves this only to `6993`;
all min-residual-sized caps still fail for every `k`.

So the low-degree product-cap route does not recover the exact bound; the
remaining proof still has to capture correlation rather than only improve the
standalone fractional cap.

## Quantified Feasibility Audit (decisive measurements)

This section re-derives the obstruction from scratch with empirical numbers and
*corrects* several earlier framings. The earlier sections kept searching for a
"correlated staircase certificate"; the measurements below show exactly which
points such a certificate would have to handle and why the kernel cannot.

### The error decomposition that matters

Write the per-input error as
`err(m,c) = approx_error(m,c)/2^72 + frac(m,c)` where
`frac = (posAccI mod 2^72)/2^72 ∈ [0,1)` is the output floor residue and
`approx_error/2^72 = delta_base(m) + top(m,c)` is the smooth EVM approximation
error (Padé/atanh error + the discarded-low-bit `log1p` term). `frac < 1` is
free (the floor bracket `posAccI < (r+1)·2^72`). So the whole proof is really a
bound on `approx_error/2^72` *correlated with* `frac`.

Key numbers (exact constants, verified against `h_int`/`accumulator`):
- Global max error = at the witness `m=39770979022059719714796403827, k=154`:
  `1.6885582527` ulp. Target bound `1.688558253` ⇒ slack at witness ≈ `3e-10` ulp.
- At the witness, `approx_error/2^72 = 0.68862949` and `frac = 0.99992876`.
  The *uncorrelated* bound `max(approx_error/2^72) + max(frac) ≈ 0.6886 + 1 =
  1.68863` exceeds the target by `~7e-5` ulp. So an uncorrelated `delta+frac`
  split CANNOT reach the target; the correlation is load-bearing. (The Python
  `ln_error_certificate.json` "certificate-closure" record is NOT rigorous:
  `verify_certificate` only checks the witness and `total_upper <= claimed_upper`
  — it never validates `delta_upper` as a global bound. It is a witness finder.)

### The bracket-precision wall (measured)

Every wide-cell route must replace the floored intermediate `H(m)=x1W(zWord m)`
by a polynomial bracket (`bracket_ge_lo`/`bracket_lt_up`). The *irreducible*
floor deviation of `H(m)` from ANY polynomial was measured by fitting deg 3/6/10
polynomials over 240-wide windows (it does not shrink with degree ⇒ it is floor
noise, not approximation error):

```text
near witness: max|H - poly| ≈ 1.5 H-units  (= 2.4e-3 ulp), increments 15..18
ge mid:       max|H - poly| ≈ 1.1 H-units  (= 1.7e-3 ulp), increments 9..11
near MHI:     max|H - poly| ≈ 1.4 H-units  (= 2.1e-3 ulp), increments 7..10
```

Conversion: 1 H-unit changes `err` by `2·RAY/2^100 ≈ 1.57e-3` ulp. So **no
polynomial-bracket cell — at any exp-sum degree, any cell width, any checker —
can prove the cut at a point whose slack is below ~0.002 ulp.** This is the real
wall, and it is independent of the `sumGEB 320` degree problem the earlier
sections obsessed over.

### Size of the exact-handling set (measured)

Points with `slack < 0.002 ulp` need exact-`H` handling (no cell works). A fine
scan (step 300) over ±3M around the witness, with best-`k` per `m`:

```text
band where err > bound - 2e-3 ulp: extends beyond ±3M (edge between ±3M and ±10M;
  envelope at ±10M is 1.669, slack 0.0196, OUT of band) ⇒ band ≈ ±5M ≈ 10M m-values
density slack<2e-3 within band: 2.34%   ⇒ ~1e5 points
density slack<1e-3 within band: 0.13%   ⇒ ~8e3 points
density slack<5e-4:             ~0.005% ⇒ ~3e2 points
density slack<1e-4:             only the witness
```

Crucially, only the **witness ripple** exceeds `bound − 0.002`. The full-domain
Padé envelope `delta_base(m)` (coarse scan, 40000 samples) exceeds the near-max
threshold over ~5% of `m` but the OTHER ripples top out at `err ≤ ~1.686`
(slack ≥ 0.0025 > 0.002), so they are fully cell-coverable. The exact-handling
set is therefore **~10^5 points, concentrated in a ~10M-wide band around the
witness (LT region, m ≈ 0.71·Sc — far from the central `[Sc-45,Sc+46)` window).**

### Why ~10^5 exact points is the blocker

The exact points have high `frac` (residue near 1), so residue / direct-residue-
gap / first-order top-budget all fail there; only the full exact `sumGEB n`
phase-direct (exact `H`, not bracketed) certifies them. They are NOT contiguous
(2.3% density, sprinkled ~every 43 m), so they cannot be wide-celled across, and
they cannot be batched into a polynomial certificate (exact `H` is not a
polynomial in `m`).

`decide +kernel` over them overflows: the **central-window theorem
`positive_shift_{ge,lt}_window_branch_all` (only ~7300 points) already stack-
overflows** (exit 134) at ~7s, with or without `ulimit -s 2000000` (the kernel's
C-level `List.all` whnf recursion is ~7300 deep — a hard C-stack limit,
unrelated to `maxRecDepth`). 10^5 is an order of magnitude worse. The two
`positive_shift_*_phase_cover_all` theorems are *also* unprovable as written:
`gePhaseCoverFastB phaseCoverFuel` is a finite-fuel cell walk that cannot cover a
2^96-wide domain, so the boolean is `false`.

### Status of the current ErrorBound.lean

Does NOT build. Independent blockers: (1) both `*_window_branch_all` decides
stack-overflow; (2) both `*_phase_cover_all` decides are `false`/intractable;
(3) the witness ripple's ~10^5 sub-0.002-ulp neighbours are handled by NOTHING
(only the single `lnErrorHardMantissa` is). `ErrorBoundCore.lean` builds clean.

### Routes that ARE feasible (for a LOOSER bound) and the real cost of the exact one

- **Feasible:** tighten the cells to ~0.002-ulp precision (achievable: the floor
  proof's own brackets + ~tens of `checkCoverK` cells per `c`, optionally with
  the factored-octave trick below) and combine with `frac < 1`. This proves a
  bound of about **1.690 ulp** (= true-max 0.6886 + bracket slop 0.0016 + 1),
  cleanly better than `df29feae`'s 1.7035, with no exact-point enumeration.
- **Factored-octave + bias improvement (new, validated numerically):** the
  `sumGEB 320` is forced only because the phase-direct route keeps the *full*
  log argument (~110–135). Factoring the octave via the existing tight
  `cap2L^(160-c)` (rational `2(10^40-1)/10^40`, 1e-40 per step) AND the bias
  constant (tighten `capBL` to ~45 digits — it is constant so this is free),
  leaves a residual argument `H/2^99 ∈ [-0.35,+0.35]` needing only an **n≈20–28**
  lower-Taylor sum (validated: octave+bias factored ⇒ min n is 20 at MHI-1, 17 at
  ge-mid, 1 at edges; LT residual is negative ⇒ needs odd-truncation / a constant
  `exp(-c)` shift to keep the residual ≥ 0). Degree ~28 instead of 320 cuts the
  Kronecker base ~10× (from the doc's ~2^592238 toward floor-proof scale ~2^5e4)
  and makes both the cells AND any exact per-point checks ~11× shallower. This
  is the right primitive to BUILD, but it does NOT cross the 0.002-ulp wall.
- **The exact 1.688558253 bound** additionally requires certifying the ~10^5
  sub-0.002-ulp points around the witness with exact `H`. The only kernel-viable
  shape is chunked exact `sumGEB n` decides (~100 chunks of ~1000 points to stay
  under the C-stack list-depth limit), which is plausibly hours of CI plus the
  machinery to (a) enumerate exactly which `(m,c)` fall below 0.002 ulp and
  (b) cover the ~10^7 cell-able points of the band between them with tight cells.
  This is a multi-day build of uncertain success, NOT a small patch.

### Recommendation

The earlier sections' search for one clean "correlated certificate" was looking
for something that cannot exist at the wide-cell level (the 0.002-ulp floor-noise
wall). The realistic decomposition is: tight factored cells everywhere with
slack > 0.002 ulp + chunked exact `sumGEB` for the ~10^5-point witness band +
the single `lnErrorHardMantissa`. Build the factored-octave primitive first
(it is reusable and de-risks both halves); then decide whether the exact-band
enumeration is worth the CI cost or whether a ~1.690 ulp bound suffices.

## CHECKPOINT: Factored-octave primitive — VERIFIED (builds clean)

New file `LnProof/FactoredCap.lean` (builds in ~19s, kernel-checked):

- **`lo_ge_pos_factored`** — the soundness bridge. It is exactly the
  `lo_ge_pos_budget_exact` assembly (`capLB_lift_right` → `capLB_pow` (octave) →
  `capLB_mul` (×bias) → `capLB_first_order_self` (×extra) → `capLB_weaken`) but
  with the **x1/H cap and the bias cap taken as parameters**. So any sharper
  `capLB ((toInt (x1W (zWord m))).toNat * 10^27) QS x1num x1den` drops straight
  in to replace the linear `x1capGeLoF`. Axiom footprint: `[propext, Quot.sound]`.

- **`capBLtight`** — sharpened bias cap. `capBL` keeps only ~31 digits
  (slop 3404 ⇒ 3.4e-28 relative ⇒ ~0.34 ulp looseness, fatal for tight cells).
  A 130-term lower sum with denominator `10^18·10^42` pins it to ~1e-39 relative.
  Proven `⟨130, by decide⟩` (~19s). Constant numerator:
  `56022770974786139918731938207935451037280277068306373453512740455438595`.

Demonstration at a tight ge point `m = 79228162514264337593543816389`
(`= MHI - 133947`), `c = 56`, slack ≈ 0.008 ulp, residual ≈ 0.347:

```text
tight bias, d=16 : false      <- degree too low: residual not captured tightly
tight bias, d=20 : true
tight bias, d=22 : true
tight bias, d=24 : true
loose bias, d=24 : true       (this point has enough slack to tolerate capBL;
                               the tightest ~0.002-ulp cells will need capBLtight)
```

So the degree needed at max residual is ~20–22 (NOT 320): the factored cut
closes once the x1/H residual (`H·10^27/QS ∈ [0, ln2/2]`) is captured by a
degree-~22 lower-Taylor cap, with the octave handled exactly by `cap2L^(160-c)`
and the bias by `capBLtight`.

### Why this is tractable (the key win)

The x1/H cap `capLB ((toInt (x1W (zWord m))).toNat * 10^27) QS x1num x1den`
depends ONLY on `m` (not `c`). So the wide-cell `checkCoverK` cover of the x1
exponential is **c-independent: ~14 cells total**, like the floor proof — NOT
~14×159 per-c cells. Each cell is a `checkCoverK` on the degree-(12·22 ≈ 264)
margin `expMargin 22 (bracket_ge_lo poly) …`, with a Kronecker base comparable
to the floor proof's `kB`. The octave/bias/`c` dependence stays in the existing
fast per-`k` budget algebra. This is why the factored reduction (320 → ~22)
crosses from intractable (`kB ~ 2^592238`, 3841-degree) to tractable.

### Remaining build steps (in order)

1. **x1 degree-22 cap cells** — generate ~14 c-independent `checkCoverK`
   literals for `capLB (H·10^27) QS (expMargin-based num) (den)` over
   `[Sc+46, MHI)` (ge) and the lt analogue. (lt residual is negative ⇒ use a
   constant `exp(-ln2/2)` shift, or odd-truncation, to keep the Taylor argument
   ≥ 0. Reuse `gen_cert_literals.py`-style Kronecker shifting.)
2. **Thread through the budget** — feed the degree-22 x1 cap (+ `capBLtight`)
   into `lo_ge_pos_factored`, with the closing inequality discharged by the
   per-`k` octave/budget algebra (mirror `errBudgetL`), to cover all
   slack > 0.002-ulp `(m,c)` in the outer regions.
3. **Exact band** — chunked flat `decide +kernel` (≤5000 pts/chunk, ~56s each;
   ~10^5 points ⇒ ~30–60 min) for the near-witness band where cells fail
   (slack < 0.002). Identify those `(m,c)` by replaying the cell predicate.
4. **Central window** — reformulate the overflowing nested `*_window_branch_all`
   decides as flat chunks (the nested `(List.range 159).all (… (List.range 46))`
   overflows the kernel C-stack at ~7s; flat 5000-pt chunks build in ~56s).
5. **Integration** — replace the unprovable `positive_shift_*_phase_cover_all`
   and wire the above into `model_ln_wad_error_bound_1_688558253`.

## Progress: x1/H degree-22 cap (Kronecker-free) — VERIFIED

Added to `FactoredCap.lean` (builds, axioms `[propext, Classical.choice, Quot.sound]`):

- **`capLB_expNum_self n p q : capLB p q (expNum n p q) (fact n * q^n)`** — the
  n-term lower partial sum is its own lower cap. Stated ABSTRACTLY (n,p,q vars)
  so `⟨n, Nat.le_refl _⟩` never makes the kernel reduce a concrete `expNum 22`
  (inlining `⟨22, le_refl⟩` stack-overflows).

- **`ge_x1_cap_d22 (h1 : Sc+46 ≤ m) (h2 : m < MHI) :
    capLB (H.toNat·10²⁷) QS (expNum 22 geTN2b.toNat geTD2b.toNat) (22!·geTD2b.toNat²²)`**
  where `geTN2b = evalPoly geTN2b m`, `geTD2b = evalPoly geTD2b m`, `H = x1W(zWord m)`.
  Proof = `capLB_arg` transport of `capLB_expNum_self 22` from argument
  `geTN2b/geTD2b` up to `H·10²⁷/QS`, using the floor bracket `geTN2b·2⁹⁹ ≤ H·geTD2b`
  (`bracket_ge_lo`) — NO Kronecker, NO degree-264 polynomial. c-independent AND
  bias-independent (H is pre-bias). The tight x1 cap the linear `x1capGeLoF` lacked.

### Build gotchas (this project has NO Mathlib — only `Init`)
- `ring`, `norm_cast`, `push_cast`, `zify`, `positivity` are ALL unavailable
  ("unknown tactic"). Use `simp only [Nat.mul_assoc, Nat.mul_comm,
  Nat.mul_left_comm]` (or `Int.*`) for reassociation, `decide` for closed
  numeric facts (e.g. `QS = 10²⁷·2⁹⁹` ⟺ the 57-digit literal), and the cast idiom
  `simp only [Int.natCast_mul, Int.natCast_pow, Int.toNat_of_nonneg h]`.
- Always `generalize evalPoly … = TN` BEFORE any arithmetic so no tactic expands
  the degree-12 Horner term (otherwise kernel stack overflow).
- Inline `⟨n, Nat.le_refl _⟩` on a CONCRETE `expNum n` overflows; route through an
  abstract helper lemma.

### What remains for a demonstrable (ge) bound
`lo_ge_pos_factored (hphase) (hx1den) (hbiasden) (hx1 := ge_x1_cap_d22 …)
(hbias := capBLtight) (hclose)` gives the upper cut. The only open piece is
`hclose` — the closing budget inequality
`posTopX·(x1den·octaveD^k·biasD·lnErrQ) ≤ x1num·octaveN^k·biasN·(lnErrQ+posAvail)·wadRayStrictDen`
with `x1num = expNum 22 geTN2b geTD2b` (degree ≈ 12·22 = 264 in m) — proven over m
by `checkCoverK` cells. This is c-dependent (octave^k, posTopX·2^k), so per-c, ~14
cells each ⇒ the bulk of the remaining engineering. The lt branch + the bias
cascade (Ln.sol margin → minimal-provable + witness) + flat-chunk reformulation of
the window decides are the other open pieces.

## KEY UNBLOCK: the octave cancels ⇒ the x1 cell cover is c-INDEPENDENT

Studying `errBudgetL` (ErrorBoundCert.lean): the budget is
`(m+1)·2ᵏ·(10⁴⁰)ᵏ·10¹⁴² ≤ 2⁹⁵·(10³¹−3401)·(2(10⁴⁰−1))ᵏ·(10³¹−3404)·(budgetCap)·…`.
The `2ᵏ·(10⁴⁰)ᵏ` on the LHS and `(2(10⁴⁰−1))ᵏ = (2·10⁴⁰−2)ᵏ` on the RHS are
equal up to the factor `(1 + 1/(10⁴⁰−1))ᵏ ≈ 1 + k·10⁻⁴⁰` — i.e. the **octave
power CANCELS**, which is exactly why `errBudgetL` proves all 160 `k` by one
closed `decide`. The residual `k`-dependence is only that ~`k·10⁻⁴⁰` factor.

Consequence for the factored route: the cut `exp(octave+bias+x1) ≥ posTopX/10¹⁸`
is `2ᵏ·(octave-looseness)·bias·exp(x1(m)) ≥ (m+1)·2ᵏ/10¹⁸`; the `2ᵏ` cancels,
leaving the **c-independent per-m inequality** `(octave-looseness)·bias·exp(x1(m))·10¹⁸ ≥ (m+1)`.
So the degree-22 x1 ripple (which is a function of the mantissa m ONLY — the Padé
error does not depend on the octave c) needs **ONE c-independent `checkCoverK`
cover (~14 cells)**, NOT 14×159. ~7 min build, tractable.

**Therefore the integration is:** (a) a per-`k` octave/bias/budget boundary
decide in the `errBudgetL` style but WITHOUT the linear x1 slop (3401) — using the
worst-`k` octave-looseness; (b) the c-independent degree-22 x1 cell cover bounding
`exp(x1(m)) = exp(H·10²⁷/QS)` from below by the ripple-tracking polynomial; (c)
combine via `lo_ge_pos_factored`. This is the concrete, tractable path to the ge
positive-shift bound. lt is the mirror (negative residual → shift). The bound's
tightness is set by how tightly the per-m x1 cell + the worst-`k` octave factor +
`capBLtight` close — pushed down to the smallest provable `lnErrorBoundNum`.

## MILESTONE: complete building proof (uniform residue, 1.7068 ulp, 3 axioms)

`LnProof.ErrorBound` now BUILDS end-to-end; `model_ln_wad_error_bound_1_7068`
depends on exactly `[propext, Classical.choice, Quot.sound]`; full `lake build`
= 96 jobs OK. This is the df29feae technique adapted to the CURRENT branch state
(current bias, current floor caps):

- ErrorBoundCert: `lnErrorCoarsePosResidue = lnErrorCoarseGePosResidue = 0`,
  `lnErrorBoundNum = 1706800000` (1.7068), `lnErrorExtraCap = 7068`. The capE*
  caps re-prove `⟨1, decide⟩` (first-order; the looser bound is easier).
- ErrorBound: `PosShiftResidueOk_uniform` / `PosShiftGeResidueOk_uniform` prove
  the coarse residue for EVERY mantissa from `posResidueGap_bounds` (`1 ≤
  posResidueGap`) since coarse = 0 ⇒ `0 ≤ posResidueGap·2²⁷·den`. Fed into the
  existing `model_ln_wad_positive_shift_{ge,lt}_residue_or_direct` consumers via
  `Or.inl`. NO phase cover, NO window decides, NO cells.

### Two gotchas hit (both now in the working proof)
1. **Stale-literal cascade**: ErrorBoundCore hardcodes `1688558253`/`688558253`
   in ~60 `decide`/`omega` goals; changing `lnErrorBoundNum` makes those reduce
   FALSE closed equalities ⇒ kernel stack overflow. Fix: sed `1688558253 →
   1706800000` THEN `688558253 → 706800000` (longer first; substring collision).
2. **`model_ln_wad_evm` must be `attribute [local irreducible]` in EVERY file
   that mentions it** (it's `local` to ErrorBoundCore). Without it in
   ErrorBound.lean, `rw`/`rfl`/`omega` try to unfold the deep EVM model ⇒
   instant stack overflow. df29feae has it at line 19; copy it.

### This is the BASELINE, not the final answer
1.7068 is the LOOSEST uniform-residue result (current bias). To satisfy "as tight
as provable" + "minimal margin":
- **Tighter bias** (minimal-provable margin + witness) lowers the uniform bound
  (df29feae's bias 0.3387 → 1.7035; minimal-provable ~0.328 → lower). Cascade:
  Ln.sol line 117 → regen (verified deterministic) → resync `Stages.BIASc`,
  `ErrorBoundCore.lnBiasI`, `FloorConsts.capBL/capBU`; re-tune so the floor proof
  still proves never-overshoot; add the minimality witness.
- **Factored cells** (`FactoredCap.lean`, all built) replace the uniform residue
  with the per-point degree-22 route for ~1.679. The c-independent octave-cancel
  cover (`hclose`) is the remaining build.

## KEY for hclose: the min-phase trick removes the staircase

`lo_ge_pos_factored`'s `hclose` contains `(lnErrQ + posAvailGe m c r)`, and
`posAvailGe m c r = lnErrArg r - posPhaseNatGe m c` depends on the FLOORED output
`r` (a staircase, not polynomial in m). But:

- `posAvailGe m c r ≥ minPosAvail` where `minPosAvail = lnPhaseExtraArg + 2²⁷·den`
  is a CONSTANT (`posPhaseNatGe_minAvail_le_lnErrArg` already in ErrorBoundCore
  ~line 3237). I.e. the floored output keeps at least the published extra ulp
  plus one residue unit of leftover.
- `hclose`'s RHS is monotone increasing in `posAvail`.

So proving the `hclose` variant with the CONSTANT `minPosAvail` in place of
`posAvail` implies the real `hclose`. The min-variant has NO staircase: it is
`posTopX·10³¹·(x1den·octaveD^k·biasD·lnErrQ) ≤
 x1num·octaveN^k·biasN·(lnErrQ+minPosAvail)·wadRayStrictDen` with
`x1num = expNum 22 geTN2b geTD2b` (degree ≈264 in m), `octave^k` per c,
everything else constant. Then the octave power cancels (errBudgetL-style,
`2^k·(10^40)^k` vs `(2(10^40-1))^k`), leaving ONE c-independent degree-264
`checkCoverK` cover (~14 cells) bounding `posTopX·const ≤ expNum22·const` over
`m ∈ [Sc+46, MHI)`.  This is the concrete, tractable remaining build for the
ge tightness (→ ~1.6906 current bias / ~1.679 minimal bias); lt is the mirror
with `posPhaseNatLt` and a sign-shifted residual.

### Next-session build order (all tools exist, all de-risked)
1. `hclose_min` soundness: checkCoverK cert (degree-264 x1 margin, c-indep) +
   octave-cancel (per-k) ⇒ `hclose` via `posAvail ≥ minPosAvail` monotonicity ⇒
   `ge_pos_cut_factored`.  Generate the ~14 shifted-Kronecker literals
   (gen_cert_literals-style; kB ≈ floor-proof scale since octave cancels).
2. lt mirror.
3. Wire into the public theorem; lower `lnErrorBoundNum` to the smallest the
   cells close (≈1.6906 on current bias).
4. Bias cascade → minimal-provable margin (≈0.3387, x1-staircase-limited) +
   witness: sed `BIASc` (122 in FloorAssembly, 31 in ErrorBoundCore) → regen →
   recompute capBL/capBU (constant, arbitrary precision) → never-overshoot →
   minimality witness. Combined with the cells ⇒ ~1.679 + minimal margin.

## Bias cascade — computed constants (current implementation)

`exact_const = floor((ln(s/2^95)+95ln2-18ln10)·10^27·2^72) =
116873961749927929127912020553113870790209010083708`.
current `BIASc = 116873961749927929127912020551506849476088469858172`,
margin = `exact_const − BIASc = 1607021314120540225536` = 0.340300 ulp.
Exact cap slop at current bias = 3403.0000 (file uses capBL 3404 = +1 conservative
for the 130-term-sum margin; capBU 3402).

Margin-reduction table (BIASc_new = BIASc + round(Δulp·2^72); slop ≈ 3403 − Δulp·10⁴):
```
Δ=0.0016 ulp → BIASc += 7555786372591432704 → margin 0.3387, exact slop 3387.0
Δ=0.0017 ulp → BIASc += 8028023020878396416 → margin 0.3386, exact slop 3386.0
Δ=0.0018 ulp → BIASc += 8500259669165361152 → margin 0.3385, exact slop 3385.0
Δ=0.0020 ulp → BIASc += 9444732965739290624 → margin 0.3383, exact slop 3383.0
```
For each, capBL slop = ceil(exact)+1 (130-sum margin), capBU slop = floor(exact)−1.
The minimal-PROVABLE Δ is whatever the floor never-overshoot proof still certifies
(x1capGeUp-staircase-limited; df29feae used Δ≈0.0016). Determine it by pushing Δ
and rebuilding FloorAssembly's never-overshoot; minimality witness = the over-estimate
peak m=40241540922992177420757753995 where, at the chosen margin, acc hits the
floor-proof binding (one slop-unit less fails the never-overshoot cap chain).

### Cascade mechanics (deterministic, df29feae-mapped)
1. `Ln.sol` line 117: `0x4ff7e9b32826a6aec97ea1e696bd71eb764c77277c` → hex(BIASc_new).
2. regen GeneratedLnModel (verified deterministic).
3. sed `Stages.BIASc` def; `lnBiasI` in ErrorBoundCore; the BIASc number literal
   (122 in FloorAssembly, 31 in ErrorBoundCore); the cap slops `3402→capBU_new`,
   `3404→capBL_new` (35 + 42 sites in FloorAssembly per memory) and in FloorConsts
   capBU/capBL.
4. rebuild floor proof (never-overshoot is the gate); then lower lnErrorBoundNum
   (uniform residue → 1 + new budget cap) and resync ErrorBoundCert capE caps.

NOTE: this is ~0.0016-ulp bound improvement (1.7068→~1.705) + the minimal-margin
clause. The BIG tightness win (→~1.6906/~1.679) is the factored cell cover, which
is independent of (and composes with) this cascade.

## EXPERIMENT: bias cascade attempted (margin 0.3403→0.3387) — REVERTED

Executed the cascade end-to-end and measured the real cost:
- Ln.sol bias `0x4ff…77277c → 0x4ff…83db7c` (BIASc += 7555786372591432704), regen
  OK (new BIASc in GeneratedLnModel, deterministic). ✓
- `Stages.BIASc` + `FloorConsts.capBL/capBU` slops `3404→3388`, `3402→3386`:
  **FloorConsts BUILDS** — the `⟨130, decide⟩`/`capUB_of_partial` verify, so the
  recomputed slops (capBL 3388, capBU 3386 for margin 0.3387) are CORRECT. ✓
- Global-sed old BIASc → new across ALL files (it appears in Stages, FloorConsts,
  FloorAssembly(122), ErrorBoundCore(31), **OctaveMono, FloorModel, FloorSpec** —
  more files than expected). ✓
- **FloorAssembly then FAILS with ~8+ errors**: `maximum recursion depth`
  (decide at 126,189,699,1319), `omega could not prove` (598,1036,1192),
  `rewrite did not find pattern` (432). These are VALUE-SPECIFIC never-overestimate
  / bracket-assembly proofs whose hardcoded bounds/patterns depend on the exact
  bias. Fixing each = the bulk of df29feae's ~506-line FloorAssembly diff.

**Conclusion (corrects the "mechanical sed" estimate):** the bias cascade is NOT
a quick sed. The literal/slop seds are mechanical, but FloorAssembly's
never-overestimate proof has many bias-value-specific `decide`/`omega`/`rewrite`
steps that each need re-derivation — genuinely the ~600-line df29feae effort.
REVERTED to the clean 1.7068 baseline (backups in scratchpad/baseline_1_7068).
The capBL/capBU slop recompute (3388/3386) and the BIASc value
(116873961749927929127912020551514405262461061290876) are CORRECT and reusable
when the full cascade is done. Future: budget the FloorAssembly proof re-derivation
as the main cost of criterion 3, not the seds.

---

## BREAKTHROUGH: ge-branch octave threading solved + cell bound 1.692115493

The "substantial remaining design problem" (how to combine the **m-dependent**
degree-22 x1/H cell cap with the **c-dependent** octave so the cut stays
c-independent) is **solved** for the ge branch. `ge_pos_cut_factored`'s open
`hclose` reduces to a single **c-independent, degree-221 polynomial inequality in
m** via three substitutions, each of which only weakens the RHS / strengthens the
LHS (so the reduced form implies `hclose`):

1. **min-phase**: `(lnErrQ + posAvailGe m c r) ≥ (lnErrQ + minPosAvail)` —
   `minPosAvail` is a constant (`lnPhaseExtraArg + 2^27·lnErrorBoundDen`), removes
   `r` and the per-`c` phase term. (Needs `minPosAvail ≤ posAvailGe`, i.e. the
   existing `posPhaseNatGe_minAvail_le_lnErrArg`-style min-phase lemma.)
2. **x ≤ (m+1)·2^k**: `wadRayNum (posTopX c m) = ((m+1)·2^k − 1)·10^31 ≤
   (m+1)·2^k·10^31`, pulls the only x-dependence into `(m+1)·2^k`.
3. **octave monotone**: after 1–2 the k-dependence is `A·(2·10^40)^k` (LHS) vs
   `B·(2(10^40−1))^k` (RHS). Dividing by `2^k`: `A·(10^40)^k ≤ B·(10^40−1)^k`
   ⟺ `A·(10^40/(10^40−1))^k ≤ B`. LHS **increases** in k; max at `k=160−c`,
   `c ≥ 1` ⇒ `k ≤ 159`. So it suffices to check at `k=159`:

   **`A·(10^40)^159 ≤ B·(10^40−1)^159`**, where
   - `A = (m+1)·10^31·22!·geTD2b(m)^22·(10^18·10^42)·lnErrQ`   (deg 221 in m)
   - `B = expNum22(geTN2b(m),geTD2b(m))·BIASCAPNUM·(lnErrQ+minPosAvail)·wadRayStrictDen`
     with `BIASCAPNUM = 56022770974786139918731938207935451037280277068306373453512740455438595`
     (the `capBLtight` num).  `expNum22(geTN2b,geTD2b)` is deg ≤220 in m.

   This is **one polynomial inequality, no c, no r** — exactly what a checkCoverK
   cell cover discharges.  (Using exponent 160 instead of 159 is a `1+10^-40`
   relative over-estimate — negligible, keep whichever is cleaner in Lean.)

**Certified bound (exact integer arithmetic, `compute_ln_error_bound.py`-style):**
the minimum `lnErrorBoundNum` for which the reduced inequality holds for **all**
`m ∈ [Sc+46, MHI)` is **1692115493 ⇒ 1.692115493 ulp**. Binding `m ≈ MHI−199501`.
This beats the current published 1.7068 AND the linear-budget ge floor 1.6994
(the floor at which `errBudgetLGe` caps out), because the degree-22 H-bracket is
much tighter than the linear `m·(10^31−3401)` y-lower-bound the budget uses.

**Kronecker tractability (validated):** relative margin `(B−A)/B` is ≈3.3e-28 over
most of `[Sc+46, MHI)`, with a mid-domain dip (≈7.6e-30 near `m=Sc+6.96e27`) and a
tight band near MHI shrinking to ≈1.2e-34 at `m≈MHI−2·10^5`. Positive everywhere
(certifiable). Cover = a few wide cells over the comfortable region + denser cells
near the mid-dip and near MHI. Degree 221 (vs the 320 unfactored ⇒ far smaller kB).
Adapt `gen_cert_literals.py` (the floor-proof deg-320 generator) to emit shifted
coefficient lists for the deg-221 margin poly per cell.

### Remaining to land criterion 2 (ge), in order
1. **Reduction lemma** `ge_pos_cut_reduced` — **DONE, builds, axiom-clean
   `[propext, Classical.choice, Quot.sound]`** (FactoredCap.lean). `hclose ⇐
   A·(10^40)^159 ≤ B·(10^40−1)^159` via subs 1–3 above + `x ≤ posTopX c m`. Pure Nat:
   `Nat.le_of_mul_le_mul_right` cancels the common `(10^40)^(c−1)` after `Nat.pow_add`
   splits `159 = (160−c)+(c−1)`; `Nat.pow_le_pow_left` for `(10^40−1) ≤ 10^40`;
   `Nat.mul_le_mul`/`Nat.add_le_add_left` for the min-phase & window-top substitutions.
   GOTCHAS: use **`Nat.le_trans`** not `le_trans` (no Mathlib); use term-mode
   `Nat.mul_assoc _ _ _` / `.symm` for the cancel-calc (bare `rw [Nat.mul_assoc]` picks
   the wrong occurrence — A0'/B0' are themselves products). The open hypothesis `hred`
   is now the ONLY thing the cell cert must supply.
2. **Cell cert**: Python emits deg-221 shifted-coeff lists for the cover cells;
   Lean `checkCoverK … = true by decide +kernel` (route `(2:Int)^n` via `Nat.pow`,
   never `unfold` the cert defs — see the perf memory).
3. **Lower `lnErrorBoundNum` to 1692115493** for the ge branch and wire the cell
   route into the ge consumer (replacing the uniform-residue ge path). Watch the
   stale-literal cascade in ErrorBoundCore (sed long-before-short).

### Global bound still gated by the LT branch
1.6921 is the **ge** number. The published bound = max(ge, lt, neg). The LT branch
(`m ∈ [2^95, Sc)`, `posPhaseNatLt`/`posBaseYLt`, **negative residual** x1W<0) needs
the analogous cell construction with the odd-truncation / shifted-residual handling,
and `M = 2^95` makes its truncation slop `10^31/2^95 ≈ 252` (vs 178 at Sc) — so the
LT cells, even when built, floor near the true worst case ~1.6885 + bracket noise
~0.002 ⇒ ~1.6906 global with the **current** bias. Tightening the 6816 bias-dominated
floor below that still needs criterion 3 (the bias cascade = the FloorAssembly
re-derivation).

### Cap floor decomposition (proven exactly, this session)
The uniform-residue per-branch min caps are **exactly** at their decide minimums:
LT=7068, GE=6994, Neg=6816 (binary-searched against the budget `decide`s — they
cannot be lowered for free). The cap `= 6816 + 10^31/M + O(k·10^-9)`, where the
**6816 floor** is `3401+3404+10+1` (the two bias-cap slops + the floor-direct slop),
and `10^31/M` is the `(m+1)/m` truncation window (252 at M=2^95, 178 at Sc). So:
cells attack the `10^31/M` term; the bias cascade attacks the 6816 floor.

---

## ge CELL CERT: VALIDATED + BUILT (octave extraction makes it tractable at kB=38000)

The whole ge cell route is now built and axiom-clean except the final small bridge.
Key unlock: **extract the octave** instead of baking `(10^40)^159` into the cell
polynomial. The collapse factor `(10^40/(10^40-1))^k` (k≤159) is bounded by the
tight rational `(10^40+160)/10^40` (looseness ~10^-40), handled by a separate
`decide` (`octaveGeBound_all`, like `errBudgetLGe_all`). This keeps the cell
polynomial at floor-proof coefficient scale.

**Measured / built (all `[propext, Classical.choice, Quot.sound]`):**
- Octave-extracted cell margin `M'(m) = B0·10^40 − A0·(10^40+160)`: **degree 221,
  max coeff 36163 bits, required kB ≈ 36562 < 38000** (the floor proof's kB works
  directly). Verified `M' = expMarginPoly 22 geTN2b geTD2b (K·(m+1)) wVal` exactly,
  where `K = 10^31·(10^18·10^42)·lnErrQ·(10^40+160)`,
  `wVal = BIASCAPNUM·(lnErrQ+minPosAvail)·wadRayStrictDen·10^40`.
- `ge_pos_cut_reduced` rewritten to the octave-extracted `hred`
  (`A0·(10^40+160) ≤ B0·10^40`) + `octaveGeBound`. **Builds, axiom-clean.**
- `certErrGeLit` (deg 221) + a **17-cell** `checkCoverK` cover of `[Sc+46, MHI−1]`:
  generated by `gen_err_cert.py`-style tooling; **each cell `decide +kernel`
  builds in 14–34 s** (`ErrCertGeC00..C16.lean`).
- `errGe_nonneg : 0 ≤ evalPoly certErrGeLit m` ∀ m∈[Sc+46,MHI−1] (`ErrCertGe.lean`,
  17-way case split + `checkCoverK_sound`). **Builds, axiom-clean.**
- Min certifiable `lnErrorBoundNum` (octave-extracted form) = **1692115493 ⇒ 1.692115493**.

**Remaining for ge (small, templated):** the bridge `certErrGe := expMarginPoly 22
geTN2b geTD2b (polyScale K [1,1]) wVal`; `errGe_eval_eq : evalPoly certErrGe =
evalPoly certErrGeLit` via `evalPoly_ext` (mirror `geLo_eval_eq`'s polyL1 chain —
note `polySub = polyAdd _ (polyNeg _)`, so use `polyL1_polyAdd`+`polyL1_polyNeg`);
then `errGe_sumGE` via **`sumGE_of_expMarginPoly`** (`hred` is exactly `sumGE 22 p q y
wVal`) + `geTN2b/geTD2b_nonneg`; AC-convert `sumGE → hred`; feed `ge_pos_cut_reduced`.

### THE COUPLING that gates a tighter *published* bound (important)
`wVal` embeds `minPosAvail`, which is defined from the GLOBAL `lnErrorBoundNum`.
Publishing 1.6921 means lowering `lnErrorBoundNum` to 1692115493 **globally** — but
the LT branch (uniform residue, `errBudgetL`) genuinely needs cap 7068 = 1.7068
(proven minimal). So the ge cells alone do NOT move the published number; a tighter
GLOBAL bound needs ALL of: ge bridge + **LT cells** (same recipe, `posPhaseNatLt`,
`posPhaseNatLt_minAvail_le_lnErrArg`, sign-flipped residual; lt cell limit ~1.6906
< 1.6921 so it clears) + neg recheck (cap 6816 < 6921, passes with more room) +
the `lnErrorBoundNum = 1692115493` stale-literal cascade in ErrorBoundCore +
rewiring both pos consumers from uniform-residue to the cell route. Global cell
bound = max(ge 1.6921, lt ~1.6906, neg 1.6816) = **1.6921** (ge-binding).

### Precision/cost roadmap (from the error model, corrected)
The residual is the HIGH-FREQUENCY accumulator phase (gap-to-1 ≈ 1.2·10⁻⁸), so
near-witness density is **~1/ε** (not 1/√ε). Tiers: (1) this O(17) wide cover ⇒
~1.6921/1.6906; (2) Regime A, O(tens) narrower cells near the envelope peak ⇒ the
phase-gap floor ≈ **1.68855825** (~8 digits); (3) Regime B, ~1/ε **width-1 exact-H
spikes** at enumerated near-max-phase m ⇒ the published 1.688558253 (~10⁵ cells).
Sweet spot to stop: ~1.68855825 unless the 10th digit is demanded. `W*` itself
moves with the Solidity margin (criterion 3), so tightest-bound and minimal-margin
stay coupled.

---

## ge cell route COMPLETE (axiom-clean) — `errGe_sumGE` proven

The full ge cell→inequality chain is now built and `[propext, Classical.choice,
Quot.sound]`:
- `ge_pos_cut_reduced` (octave-extracted soundness: `hred ⇒ ge upper cut`),
- `octaveGeBound` (octave-collapse `decide`),
- `certErrGeLit` + 17 `checkCoverK` cells + `errGe_nonneg` (cover, builds in 14–34 s/cell),
- `ErrCertGeBridge.lean`: `certErrGe = expMarginPoly 22 geTN2b geTD2b (polyScale errGeK [1,1]) errGeW`,
  `errGe_eval_eq` (`evalPoly_ext`), `errGe_sumGE` (`sumGE_of_expMarginPoly`).

`errGe_sumGE` proves the ge cells discharge the tight `sumGE 22 … errGeW` inequality
(= `hred` in `sumGE` form), i.e. the cells certify the 1.692115493 budget for the ge
branch. So the hardest branch's entire cell machinery is done.

**Build gotchas discovered (record for the LT replica):**
- In `errGe_eval_eq` obligation 1 (the symbolic polyL1 bound) DON'T `unfold`/`rw` — state
  the bound on the `…Lit` bases and close by DEFEQ `exact` (mirrors `geLo_eval_eq`).
  `unfold … polySub; rw [geTN2b_eq_lit,…]` there → kernel stack overflow.
- Convert Nat domain bounds `Sc+46 ≤ m` / `m < MHI` to the Int bounds the cert wants with
  `simp only [Sc]/[MHI]; omega` (the FloorCaps pattern). `exact_mod_cast` on the
  ~29-digit literals → stack overflow.
- `hfin` (obligation-1 numeric `decide`) and obligation-3 (`eval`-at-`2^kB` `decide`)
  both build (~1–6 s). Bisect overflows by building each obligation as a standalone
  theorem in a scratch file (with `import LnProof.FactoredCap` for `expMarginPoly`).

### Still remaining for a tighter PUBLISHED bound (the gate = LT branch + cascade)
The cert's `errGeW` embeds `minPosAvail` at `lnErrorBoundNum = 1692115493`, while the
codebase global is 1706800000. Landing a tighter published bound needs (together):
1. **LT cells** — a full parallel construction (no shortcut): `lt_pos_cut_reduced`
   (FactoredCap has only the ge analog), `ltTN2b/ltTD2b` cap with the NEGATIVE-residual /
   `capUB` structure, `certErrLtLit` + cover + `ErrCertLtBridge`. LT is the GLOBAL gate
   (uniform-residue LT cap 7068 is proven minimal; LT cell limit ~1.6906 < ge 1.6921, so
   global = 1.6921 ge-binding — or ~1.6910 with per-cell min-phase per the measured model).
2. **`lnErrorBoundNum = 1692115493` cascade** — sed the stale literals
   (`1706800000→1692115493`, `706800000→692115493`) in ErrorBoundCore; the per-branch
   residue caps (6994/7068) then exceed the 6921 target, forcing BOTH pos branches onto
   the cell route (this is why both ge and lt cells must land before the cascade).
3. **neg / c160 / r=−1 rechecks** at 6921 (neg cap 6816 < 6921 ✓ with room).
4. Rewire both pos consumers off uniform-residue; restate the public theorem at 1.692115493.

Measured ladder (this session): proven 1.7068 → df29feae 1.7035 → cheap O(tens)-cell
sweet spot ~1.6910 → pre-floor O(hundreds) ~1.6889 → ~10⁵ width-1 spikes = the published
1.688558253 (= true global worst W*). The cells convert "1.7068 proven" into "~1.691
proven at O(tens) cells" — ~93% of the 0.0182-ulp gap; the last ~7% is the 1/ε spike tail
imposed by the implementation's high-frequency floored accumulator.

---

## PHASE 1 DONE: bias cascade to 0.3387 ported into the main tree (1.7035, axiom-clean)

The bias-0.3387 cascade (the criterion-3 blocker) is solved by **adopting commit
df29feae's already-fixed floor layer** rather than re-deriving FloorAssembly:

1. `git checkout df29feae -- Stages FloorConsts FloorCertDefs FloorAssembly
   FloorBudget FloorCaps FloorWindow FloorModel OctaveMono FloorSpec` + all
   `FloorCert*C*` cell covers (df29feae re-partitioned them at the new EUN).
2. Regenerated `FloorCertLit` at **EUN 3385** (`gen_cert_literals.py`: `EUN=3385`)
   — the floor cert polys shift with EUN, so the literals must be regenerated.
3. `Ln.sol` bias add-const → `0x4ff7e9b32826a6aec97ea1e69728fb233885bebd9c`;
   `GeneratedLnModel.lean` line-125 `evmAdd` const → `…514598262029661683100`
   (the model's bias is a SINGLE additive constant — no EVMYulLean/Yul regen needed;
   the ln proof imports only `Init`, no EVMYulLean dep).
4. Cascaded MY error-bound layer (`ErrorBoundCore`/`ErrorBoundCert`, kept — my
   structure differs from df29feae's monolithic `ErrorBound`):
   - slops every form: `10^31 - 3401→3385`, `-3404→3387`, `(10:Nat)^31 - …`,
     `ten31 - …`, AND the literal `9999…96599→…96615` (=10^31-3385). **GOTCHA:**
     the literal-form sed and the `rw [show (…96615) = 10^31 - 340X]` proofs must
     stay consistent (a mismatched `show` → false `decide` → kernel stack overflow).
   - the OLD BIASc literal appears **30×** in ErrorBoundCore (not via the `BIASc`
     name) — sed `…506849476088469858172 → …514598262029661683100`; `lnBiasI` too.
   - boundNum `1706800000→1703500000`, `706800000→703500000`; caps `7068→7035`
     (extra/CoarsePos), `6994→6961` (CoarseGePos), `6816→6785` (CoarseNeg),
     `lnErrorBiasCap 3403→3387`.

Result: `model_ln_wad_error_bound_1_7068` (name stale) proves the cut at
`lnErrorBoundNum=1703500000` = **1.7035 ulp**, `[propext, Classical.choice,
Quot.sound]`, full `lake build` 96 jobs. New-bias caps (recomputed, exact min):
pos 7035 / ge 6961 / neg **6783** (≤6788 ⇒ neg branch clears 1.6788 via uniform
residue, no cells). New-bias ge-cell `BIASCAPNUM` (capBLtight, ⟨130⟩) =
`56022770974786139918731938208027377079380304244461953777704904393546003`.

## PHASE 2 (remaining): cells → 1.6788
- **ge cells**: regenerate cert at new bias; uniform-minPosAvail gives **1.690474624**
  (computed). Reaching 1.6788 needs **per-branch/per-cell min-phase** (§6 of
  PRECISION_ANALYSIS): replace the constant `minPosAvail` (= global, LT-tight, gap≥1)
  with the larger ge-region availability (gap > 1 over ge), draining ~0.0117. This is
  the key new sub-technique; "cheap, just per-cell constants" but needs a per-cell
  `posResidueGap ≥ G_cell` lower bound feeding a per-cell `minPosAvail`.
- **lt cells**: parallel construction (negative residual, `capUB`, `lt_pos_cut_reduced`).
- Lower `lnErrorBoundNum → 1678800000`; rewire ge+lt consumers off uniform-residue
  onto the cell route; recheck c160 / r=-1 cases clear 6788; rename the public theorem.

---

## CHECKPOINT FINDING: §6's "cheap per-cell min-phase" is INCORRECT (measured at new bias)

User goal switched to **1.6788 ulp via bias 0.3387**. Phase 1 (bias cascade) is DONE
(1.7035 at 0.3387, axiom-clean — see above). Investigating the ge branch toward 1.6788
("ge first, checkpoint"), I measured the residue-gap structure of the model
(`gap(m,k) = 2⁷² − (acc mod 2⁷²)`, `acc = K·h_int(m) + LN2·k + BIAS`):

- **`gap ≈ 1 ⟺ maximum error`** — the floored-away part is exactly `2⁷² − gap`, so the
  worst-case (max-underestimate) inputs are precisely the gap≈1 points.
- **`d(acc mod 2⁷²)/dm ≈ K·16 ≈ 2⁶⁷` per m** ⇒ `acc mod 2⁷²` wraps the full `[0,2⁷²)`
  range every **~32 mantissas**. So gap≈1 (near-worst) points recur every ~32 m.
- At a *single* m, the min gap over the 160 valid k is ~`2⁶⁴` (huge availability);
  but any **wide cell** (the octave-extracted cover uses cells ~`6·10²⁷` wide) contains
  gap≈1 points, so its min gap collapses to ~1 ⇒ per-cell min-phase over wide cells
  gives **no** improvement.

**Conclusion (corrects PRECISION_ANALYSIS §6):** per-cell/per-branch min-phase is NOT
"cheap (just per-cell constants)". To drain the uniform-`minPosAvail` slack you must
make cells **narrow enough (~width-32 m, i.e. thousands–millions of cells over the
binding band) to separate the high-gap m's from the recurring gap≈1 m's**. This is the
Regime-B (width-≪32 / exact-H) cost, NOT a cheap refinement. The earlier "uniform 1.6921
slack is almost entirely min-phase" tracing was misleading: the wide-cell binding
(MHI−4·10⁵) is a low-error, high-gap m whose loose bound comes from the cell polynomial
(H-bracket/octave) interacting with `minPosAvail`, and you cannot lower it without
either (a) narrow cells that isolate it from the gap≈1 band, or (b) pre-floor bracketing
to kill the ~0.0016-ulp H-slop. Both are the expensive precision tail.

**Implication for 1.6788:** the new-bias true ge worst ≈ 1.677 (old-bias ge worst
1.6787840 − ~0.0016 bias shift); the target 1.6788 sits ~one H-unit (~0.0016 ulp) above
it, so reaching it needs the finer cover (width-~32 near the binding band) PLUS the
H-bracket — well beyond the ~17 wide octave-extracted cells. **Recommendation:** before
committing Lean effort, settle the exact achievable-bound-vs-cell-count curve at the new
bias (the error-interval Python selftest rejects the new bias — its `constant_intervals()`
bias-floor assertion must be updated to the 0.3387 bias to measure the true new-bias ge
worst and the binding-band width).

---

## DECISIVE FEASIBILITY RESULT: 1.6788 is NOT reachable via the octave-extracted cells

Measured at the new bias (0.3387), with the new-bias capBLtight `BIASCAPNUM` and the
uniform `minPosAvail`:

- New-bias **true ge worst ≈ 1.6782542** (sampled, m=MHI−1194901). Target 1.6788 sits
  only ~0.0006 ulp above it.
- **Uniform ge cell boundNum exceeds 1.6788 over a band of width ~2⁸⁰** — precisely,
  `boundNum_uniform(m) > 1.6788` for all `m ∈ [MHI − 2308742482303854085132085, MHI)`
  (≈2⁸⁰). `boundNum_uniform(MHI−1) = 1.690474624`.
- Fixing that band with the per-cell min-phase requires cells narrow enough (~width-32,
  since gap≈1 points recur every ~32 m) to separate high-gap from gap≈1 m's: that is
  **~7×10²² cells**. Infeasible by ~18 orders of magnitude.

**Root cause (definitive):** the octave-extracted cut abstracts the model output `r`
through a *single constant* `minPosAvail` = (gap ≥ 1, the GLOBAL floor, achieved at the
true-worst points). Over the near-MHI band the actual residue-gap is ~2⁶⁴ (so the true
error there is low, ~1.0 ulp), but the cut cannot exploit it — it is forced to use gap=1,
yielding 1.6905. The ONLY way to use the actual per-input availability is the tight
**direct-phase route** (`PosShiftGePhaseDirectOk`, `sumGE 320`) — the degree-320
single-decide that is intractable (the very problem the octave cells were introduced to
avoid). The per-cell phase cover that would bridge them is the 2^96-leaf cover already
shown false ("finite fuel can't cover 2^96").

**Conclusion — corrects the goal's premise and PRECISION_ANALYSIS §5–6:** with the
documented techniques, the axiom-clean achievable bounds at the 0.3387 bias are
**1.7035** (uniform residue, BUILT) or **~1.6905** (octave-extracted cells, ge-binding,
if the ge+lt cell routes are completed). **1.6788 is below the cell route's ~1.6905
floor** and is NOT reachable without a tight direct-phase route, which is intractable.
PRECISION_ANALYSIS §6's "per-cell min-phase is cheap" and §5's "cheap O(tens)-cell sweet
spot ~1.6910" do not get to 1.6788 — and at the new bias the cell floor itself (1.6905)
is the wall, not 1.6788. The "1.6788 via bias 0.3387" target appears infeasible with the
present technique set; reaching it needs a fundamentally new tractable-yet-tight phase
argument (none is known in this codebase).

---

## CORRECTION to the "DECISIVE FEASIBILITY RESULT" above (min-phase attribution was WRONG)

The section "1.6788 is NOT reachable via the octave-extracted cells" blamed the ~0.012-ulp
ge cell slack on the uniform `minPosAvail` (min-phase). **That attribution is arithmetically
wrong:** `minPosAvail ≈ 2^128` while `lnErrQ ≈ 2^219`, so the min-phase term is only ~2^-90
RELATIVE — it cannot produce a 7e-3 (=0.012/1.69) relative slack. The 2^80-band /
narrow-cell infeasibility argument therefore does NOT apply (it was predicated on the slack
being min-phase). The slack is in the **H-bracket / phase envelope**, which is addressed by a
DIFFERENT family of techniques that do NOT need narrow cells:

- **Curved `x1W` rational-bracket phase envelope** (lines 808–975, "the current best route"):
  uses the per-`m` floor brackets `geTN2b·2^99 ≤ x1W·geTD2b` as a moving lower envelope, so the
  interval inequality is a c-independent polynomial-in-`m` (Kronecker `checkCoverK`). Bridges
  `gePhaseLowerMargin_sound`/`sumGE_arg_mono`/`posPhaseNatGe_cast_decomp` BUILD axiom-clean;
  only the cover/table was never generated. kB≈38000 (tractable). This is c-independent AND
  tighter than uniform-minPosAvail.
- **Pre-floor bracketing (Regime A)**: track the smooth pre-floor `V` (rational in `m`, exactly
  bracketable), carry the floor as `H ≥ V−1`. Polynomial part exact; residual = 1 H-unit
  (1 unit of H → `K/2^72 ≈ 2^-9.3 ≈ 0.0016 ulp` of output). Drops the ge cell floor toward
  `true_worst + 0.0016`.

**RAZOR-THIN feasibility window (must re-measure before building):** new-bias true ge worst
≈ 1.6783; target 1.6788 ⇒ headroom ≈ 0.0005 ulp; pre-floor residual ≈ 0.0016 ulp. So
`true_worst + 1_H_unit ≈ 1.6799` which is > 1.6788 IF true_worst = 1.6783. Whether 1.6788 is
reachable hinges on (a) the exact new-bias true ge worst (my 1.6783 is a sampled upper bound —
the true global ge worst may be lower, e.g. ~1.677, giving room), and (b) whether the curved
bracket's residual is really ≤ 0.0005. **Highest-value next step: exact-integer re-measurement
at the 0.3387 bias of the pre-floor-bracketed ge cell floor.** If it is ≤ 1.6788, build
Candidate A + pre-floor bracketing; if > 1.6788, no documented tractable technique closes it.

---

## CORRECTED PATH TO 1.6788 (the "floors at 1.6793" pessimism was also wrong)

After the slack ablation (H-bracket 0.0112 + window 0.0126) I claimed the cell route
"floors at ~1.6793". That is the **wide-cell, exact-H** bound; it is NOT a hard floor.
Correct decomposition of the ~0.0021 ulp gap between the wide-cell exact-H bound
(≈1.6809 old / ≈1.6793 new) and the true worst (≈1.6788 old / ≈1.677 new):

1. **H-bracket slop (0.0112 ulp):** `geTN2b/geTD2b` lower-brackets the floored |H| ~7
   H-units low. **Fix = pre-floor bracketing**: bracket the SMOOTH pre-floor
   `V = p·z/q` (the value before the final `sdiv` in `h_int`; on ge `V>0`, `H=trunc(V)`,
   so `H ≥ V−1`) with a TIGHTER degree-12 polynomial lower bracket (within ~1 H-unit
   instead of 7), and feed that to the degree-22 x1 cap. Removes ~0.0096 ulp.
2. **Window term (0.0126 ulp) = `RAY·ln((m+1)/m)`:** this is REAL block-quantization
   error (the model emits one `r` per mantissa block; the error genuinely grows to the
   block top `posTopX`). It is PART of the true worst and cannot be removed — the true
   worst legitimately includes it.
3. **m-range conservatism (~0.0021 ulp):** a WIDE cell's polynomial bound over its
   m-range exceeds the per-m true worst in that range. **Fix = moderately narrower cells
   near the binding band** (the error envelope is smooth — H-bracket + `1/m` window — so
   the high-freq phase is already handled by the negligible min-phase term; a few-fold
   narrower cells near MHI reduce the conservatism by the needed ~0.0005 ulp). This is a
   MODEST refinement (hundreds–thousands of cells near the binding), NOT the 2^80/
   width-32 explosion (that explosion was the bogus min-phase attribution).

**REVISED FEASIBILITY: 1.6788 appears REACHABLE** via: (a) pre-floor bracketing (tighter
`V`-bracket, ≤1 H-unit) + (b) a non-uniform cover with narrower cells near the binding
band + (c) the lt-branch analog + (d) `lnErrorBoundNum→1678800000` cascade & wiring. The
min-phase / 2^80-infeasibility conclusions earlier in this file are WRONG (min-phase is
~2^-90 relative, negligible). The real cost is building the tighter V-bracket and the
non-uniform cover — substantial but tractable, NOT astronomically infeasible.

**Build order:** (1) generate a degree-12 lower bracket of the smooth `V` within 1 H-unit
(adapt the minimax bracket derivation; Python); (2) Lean lemma `H ≥ V−1` + swap it into
`ge_x1_cap_d22`/`ge_pos_cut_reduced`; (3) regenerate the ge cert at new bias with the
tighter bracket + a non-uniform (binding-band-refined) cover; (4) measure the achieved ge
bound — if ≤1.6788, proceed; (5) lt analog; (6) boundNum cascade + wire. The decisive
open number is the achieved ge bound after (1)-(3); compute it by re-running the cell
bound with the tighter V-bracket, NOT by sampling the true worst (intractable).

---

## FINAL CORRECTED UNDERSTANDING (supersedes ALL earlier feasibility claims above)

After several wrong feasibility flips (all from conflating the cell route's LOOSE bound
with the true error), the directly-measured facts at the 0.3387 bias are:

- **TRUE ge worst ≈ 1.678** — `ln_error_interval` (the model's exact error, window
  included) gives **1.6783** at m=MHI−162053 and **1.6612** at the mid-domain cell-binding
  m. So **1.6788 is a VALID bound** (above the true worst). [Earlier "1.6788 is FALSE /
  below the worst" was WRONG.]
- The octave-extracted cell route overcounts the true error: at the mid-domain m it
  certifies **1.6816** (exact H) while the true error there is **1.6612** — an overcount
  of **~0.020 ulp**. So the cell route's bound (~1.6816 exact-H / ~1.6905 with the
  geTN2b bracket) is LOOSE, NOT the true worst.
- The overcount has TWO sources, both cell-route looseness (NOT real error):
  1. **H-bracket slop ~0.011** (geTN2b/geTD2b vs |H|) — fix = pre-floor bracketing.
  2. **octave/window-collapse slop ~0.02** — the c-independent octave collapse bounds the
     cut for the worst c and bounds x by the full block top `(m+1)·2^(160−c)`, which
     overcounts the per-c true error (true worst-k error 1.6612 vs collapsed 1.6816).
     This is the "phase / anchor-at-block-top" lever: a tighter per-c (or per-k-bucket)
     handling, instead of the single worst-case octave collapse, recovers this ~0.02.

**REVISED, CORRECT FEASIBILITY: 1.6788 is reachable.** The true worst (~1.678) is below
it; the obstacle is purely the cell route's ~0.03 overcount (H-bracket + octave-collapse),
both of which are tightenable WITHOUT infeasible cell counts:
- pre-floor bracketing removes the H-bracket ~0.011;
- a tighter octave/window handling (per-c bucketing, or anchoring the cut at the block-top
  mantissa rather than the worst-case collapse) removes the ~0.02.

The min-phase / 2^80-band / "floors at 1.6793 or 1.6816" claims earlier in this file are
ALL superseded by this section — they were cell-route-looseness artifacts, not the truth.
The build: (1) tighten the octave/window collapse (the bigger ~0.02 term — likely the
"promising phase technique" the user recalls); (2) pre-floor bracketing (~0.011);
(3) measure the tightened ge cell bound (target ≤1.6788); (4) lt analog; (5) boundNum
cascade to 1678800000 + wiring.

---

## GRIND STEP 1 RESULT: bracket slop measured; the polynomial-bracket route floors at ~1.6799

Measured the ge x1/H bracket slop `(H·geTD2b − geTN2b·2^99)/geTD2b` over the ge domain:
- **Varies 0.072 → 9.110 H-units** (1 H-unit = RAY/2^99 ≈ 0.001578 ulp). The SLOP margins
  (`SLOPPc`/`SLOPQc` in `build_branch`) are already near-minimal (min slop 0.072), so the
  ~9-unit max is the **degree-12 polynomial fit error**, varying with m — NOT a uniform
  offset that can be shaved.
- The built cell route (1.6904746) **binds at m=MHI−499801, where slop = 8.11 H-units
  (0.0128 ulp)** — the bracket IS the dominant overcount there.

**Hard constraint (the key new finding):** the bracket lower-bounds the FLOORED H, so a
*polynomial* bracket cannot beat **~1 H-unit** (it must dip below `V−1` across the floor's
unit jumps; H=trunc(V), V−H∈[0.22,0.75], and the poly can't track integer steps). A perfect
1-H-unit bracket gives `(true ge worst ≈1.6783) + 1_H_unit ≈ 1.6799` — **still ~0.001 ulp
above 1.6788.** The remaining ~0.001 (≈0.7 H-unit) needs **exact-H width-1 cells** at the
near-worst band; the precision doc's density (~16% of points within 1e-3 of max) implies
that band is a large fraction of 2^95 m's ⇒ likely infeasibly many width-1 cells.

**Confidence caveat:** the headroom (1.6788 − 1.6783 ≈ 0.0005) is BELOW one H-unit, i.e. at
the floored accumulator's own granularity. My Python cell-bound reconstructions carry a
confirmed ~0.02-ulp bug (disagree with the authoritative `ln_error_interval`), so the
≤1.6788-vs-1.6799 question CANNOT be settled outside Lean. Whether 1.6788 is reachable hinges
on (a) the exact true worst (≈1.6783±, needs a rigorous witness search, not float/sampling —
catastrophic cancellation), and (b) whether the near-worst band needing exact-H cells is
small enough — both currently unresolved.

**Honest status of the grind:** step 1 (measure/tighten the bracket) shows the
polynomial-bracket route floors at ~1.6799, ~0.001 above target; closing it needs exact-H
spikes whose count may be infeasible. This is the same razor's-edge wall the floored
accumulator imposes (the published-target 1.688558253 was always the ~10^5-spike regime).
The bias-0.3387 / 1.7035 proof remains the solid, verified deliverable.

## GRIND STEP 2 RESULT (KERNEL, not Python): ge cell cap is ~1.6921, and the bracket gap at the binding is irreducible

This session settled the open ≤1.6788-vs-floor question **in Lean** (the prior
"~1.6799" was a Python estimate the doc itself flagged as un-settleable outside Lean).

**Method.** Verified-correct regeneration: a Lean `#eval` generator (`GenCertErr.lean`,
in scratch backup) recomputes `errGeW = BIASCAPNUM·(lnErrQ+minPosAvail)·wadRayStrictDen·10^40`
and `certErrGeLit = trim(expMarginPoly 22 geTN2b geTD2b (polyScale errGeK [1,1]) errGeW)` for
any target `lnErrorBoundNum`. Sanity-checked: at `1692115493` it reproduces the committed
`errGeW` and `certErrGeLit` **byte-for-byte** (`==` true, 222 coeffs). Then regenerated at
lower targets and rebuilt the binding cell `ErrCertGeC16` (the MHI cell,
`[78082016047349163698545554609, MHI−1]`), letting `decide +kernel` adjudicate `checkCoverK`.

**Kernel results (ge branch, current bracket, new bias 0.3387, BIASCAPNUM ...438595):**

| lnErrorBoundNum | C16 `checkCoverK` |
|---|---|
| 1692115493 | **PASS** (validates pipeline = committed cert) |
| 1691000000 | FAIL |
| 1690474624 | FAIL (← doc's claimed "uniform ge cap"; kernel says it is FALSE) |
| 1685000000 | FAIL |
| 1678800000 (target) | FAIL — `decide proved ... = true is false` |

So the **kernel-certified ge cell cap is ~1.6915–1.6921**, NOT the 1.6904746 the doc claimed.
The doc's Python ge-cap was optimistic by ~0.0015. Gap to 1.6788 is **~0.013** (kernel-confirmed).

**Why per-floor / per-cell / curved bracketing CANNOT close it (structural, from Stages.lean):**
- The bracket gap `slop(m) = H_actual(m) − bracket(m)` is propagated by `scaled_mul_step`
  with `U = Uc` = the **global** max of `u` over the whole domain. The per-floor slops
  `SLOPP1..3`/`SLOPQ1..4` are each one floor-unit; `SLOPPc/SLOPQc` are them propagated, and
  the early-stage floors dominate (multiplied by `Uc^(remaining ×u)`).
- The binding cell C16 spans m where `u = uWord(zWord m) ∈ [0.92·Uc, Uc]` (computed: at m=MHI,
  `u=Uc`; at C16's low end, `u=0.92·Uc`). So the uniform `Uc` factor is **already tight at the
  binding** — a per-cell `Uc_cell` gives no reduction on C16.
- The gap is **high-frequency** in m (the floor fractions decorrelate per m; gap ranges
  [0.072, ~9] H-units, GRIND STEP 1). `checkCoverK` needs margin ≥ 0 over the WHOLE cell, so it
  is set by the **max-gap m** in the cell. Max-gap m's (real_loss≈0) are dense (recur every few m).
  Any cell of width > a few m contains one ⇒ bracket must sit ~9 units below `H_actual` there.
- **Pre-floor bracketing does NOT reach 1 H-unit.** The "smooth V" is `p·z/q` with FLOORED
  intermediates; `H_actual` is up to ~9 units below the *ideal* smooth P/Q (the intermediate
  floor losses), high-frequency. Removing only the FINAL division's frac (~1 unit) leaves the
  ~8-unit intermediate-floor gap. The doc's "perfect 1-H-unit bracket ⇒ 1.6799" is unfounded.

**Conclusion (kernel + structure):** the ge cell route floors at ~1.6921. The ~0.013 gap to
1.6788 is irreducible high-frequency intermediate-floor noise at the MHI binding; no polynomial/
rational bracket (per-floor, per-cell, curved) can remove it over a multi-m cell. Closing it
requires exact-H width-1 cells over the band where `envelope+gap > 1.6788`, which (gap high-freq,
~16% density within 1e-3 of max per the precision doc) is a large fraction of ~2^某 m's —
astronomically many. **1.6788 is not reachable via the cell route at this bias.**

The bias-0.3387 / 1.7035-ulp axiom-clean proof remains the verified deliverable. Wiring the
existing ge+lt cells + cascade would publish ~1.692 (a real improvement over 1.7035), but not 1.6788.

## DECISIVE (2026-06-23): 1.6788 is FALSE at the deployed bias — the goal is impossible

Verified THREE independent ways (trusted Lean model + bc; NOT the stale Python):

1. **Stale-model root cause.** The "authoritative" Python error model is pinned to the OLD 0.3403 bias, not the deployed 0.3387:
   - `check_ln_counterexample.py:31` `_BIAS = 0x4FF7E9B32826A6AEC97EA1E696BD71EB764C77277C` = 116873961749927929127912020551506849476088469858172
   - `compute_ln_error_bound.py:40` `MARGIN = 1607021314120540225536` (= 0.3403 ulp)
   - DEPLOYED `Ln.sol:117` bias = 0x4ff7e9b32826a6aec97ea1e69728fb233885bebd9c = 116873961749927929127912020551514598262029661683100 (margin 1599272528179348400608 = 0.3387 ulp); Lean `GeneratedLnModel:125` matches.
   - They differ by exactly 7748785941191824928 (= the margin delta). So `ln_error_interval` as-committed computes the error at the WRONG bias, ~0.0016 ulp off. Every "1.6788 achievable at 0.3387" claim (goal premise, memory, precision doc) rests on this stale constant.

2. **Explicit witness (rigorous, exact).** x = 11738321145292912533371892013356416013171393822719 (LT branch, m=39770979022059719714784307619, k=68):
   - Trusted Lean `model_ln_wad_evm x` = 71540411591039112565634317102 (exact #eval).
   - True L = ln(x/1e18)*1e27 = 71540411591039112565634317103.68658611134... (bc scale 60).
   - error = L − r = **1.68658611… ulp > 1.6788**. So `error < 1.6788` is FALSE; proving it would be unsound.

3. **Consequence.** W*(deployed 0.3387) ≈ 1.687 (old W*=1.6885582527 at 0.3403, minus the 0.0016 margin change). The minimum *true* (hence minimum provable) bound at this bias is ~1.6866 — NO certificate/bracket/cell technique can go below it. The kernel ge-cap 1.6921 and explorer 3's true-u bracket (which would reach ~W*) are all bounded below by W*≈1.6866.

**To actually reach 1.6788** the bias MARGIN must be cut by ≳0.008 ulp more (to ≈0.330, the minimal-provable margin per §8), which requires RE-DERIVING the never-overshoot (FloorAssembly) at the tighter bias (the hard multi-file cascade, per memory the 0.3387 cascade itself was the blocker) AND then a tight error bound (explorer 3's true-u bracket route A) to certify down to ~W*(0.330)≈1.6779 < 1.6788. Both are large; neither is the "just apply a technique" the goal assumed.

**ACTION ITEM:** fix the stale `check_ln_counterexample._BIAS` / `compute_ln_error_bound.MARGIN` to the deployed values, or all future Python analysis stays 0.0016 ulp wrong.

## CRUX RESOLVED (2026-06-23): the ~6-unit box loss is INTRINSIC at feasible cell granularity — feasible floor ≈ true_worst + 0.0142, bias-independent

The true-u re-anchoring (which looked like the lever to beat the kernel-measured 1.6921 ge cap) does NOT survive a wide-cell cover. Four independent structural confirmations:
1. `checkCoverK` (KroneckerShift.lean:248) is strictly UNIVARIATE in m. The true u = ⌊q(m)²/2¹⁰⁴⌋ is two stacked floors, not a polynomial in m, so any wide cover must replace u by a continuous surrogate s(m) ∈ [Qarg(m), Parg(m)].
2. Over the binding cell C16, `true_u(m) − Qarg(m)` equidistributes across the full box width [0.004, 1.019] (5/50/95% = 0.06/0.50/0.96). So at the worst m in the cell, |true_u − s(m)| ≈ 1 u-unit, × poly slope (~6 H-units/u-unit) = ~6 H-units lost — IDENTICAL to the box bracket. The divided-difference loss is relocated (Parg−true_u → true_u−s(m)), not removed.
3. A Positivstellensatz (polynomial-multiplier) cert can't evade it: the real-relaxation of the floor constraints {q,u} has a ~1.02-u-unit band per m; the integer-pinned tight curve (exactly 1 valid q,u per m) is visible ONLY to per-m integer reasoning.
4. Keeping <1 H-unit ⇒ cells ~residue-run-wide (~6 m); C16 alone (~2⁸⁹ m) ⇒ ~2⁸⁷ cells vs 17 wide cells. Infeasible.

**The box width ≈1.02 u-unit is the u-FLOOR span (frac(z²/2¹⁰⁴)), inherent to the algorithm's `u = z²>>104` step; the ~6 H-units/u-unit slope is the minimax poly's derivative. Both are bias-INDEPENDENT (H is pre-bias).** So the feasible (wide-cell) proof floor = true_worst(bias) + ~0.0142 (box loss) + residual, irreducible by any per-floor/per-cell/curved/true-u/Positivstellensatz technique at feasible `decide` granularity.

CONSEQUENCES (rigorous):
- ge cell cap = 1.6921 (kernel) = ge_true_worst(1.6779) + box_loss(0.0142). ✓ self-consistent.
- LT branch holds the GLOBAL true worst (1.68659, witness-verified). LT cell cap ≈ 1.68659 + box_loss ≈ 1.70 at bias 0.3387 → the global feasible cell floor at 0.3387 is ≈1.70 (only marginally below the proven uniform 1.7035).
- At the MINIMAL-provable margin (~0.330, the lowest bias the never-overshoot survives), global true worst ≈1.6779 → feasible floor ≈1.6921. **So ~1.6921 is the BEST feasible bound at ANY valid bias.**
- **Target 1.6866 (true worst at 0.3387) and 1.6788 are BELOW the feasible floor at every valid bias.** They are TRUE (1.6866 > witness 1.68659) but require exact per-m cells over {true_error > target − box_loss} ≈ a large fraction of the unimodal LT peak ⇒ ~2⁸⁷ cells. Infeasible.

**Honest deliverables at bias 0.3387:** (proven) 1.7035 axiom-clean; (feasibly buildable, real work) ge cells 1.6921 + LT cells ≈1.70 global ⇒ marginal ~0.003 gain; (BEST feasible, needs minimal-margin bias 0.330 + FloorAssembly never-overshoot re-derivation + cells) ≈1.6921. 1.6866/1.6788 not feasibly reachable.

## MEASURED (2026-06-23): the deficit envelope is BROAD-FLAT → the near-worst band is ~5e25 m → 1.6866 infeasible by ~18 orders

Revisited the "1.6866 infeasible" conclusion by DIRECT measurement (trusted Lean model `accOf` = pre-floor r_4 + bc for L), per the directive to check whether recommendations are wholly incorrect. Result: confirmed, and now the ROOT CAUSE is measured.

Deficit `D_top(m) = ln((m+1)·2^68−1 / 1e18)·1e27 − accOf(m·2^68)/2^72` (top-of-block, k=68, LT branch), around the witness m=39770979022059719714784307619:
- offset −1e26: 0.462 | −3e25: 0.668 | −1e25: 0.683 | −3e24: 0.685 | **0: 0.6860** | +3e24: 0.682 | +1e25: 0.683 | +3e25: 0.670 | +1e26: 0.568 | +2e26: 0.351.

The deficit peak (= bias + minimax approx error, max D_top=0.6866 = the witness worst 1.68659 − phase) is **UNIMODAL but BROAD-FLAT**: D_top stays within 0.003 of its max over **±1e25 m**. Consequences for proving error < 1.6866:
- Wide cells (box bracket, box_loss~0.0142 + uniform residue) fail where D_top > 1.6866 − 1 − box_loss = 0.6724. MEASURED band {D_top>0.6724} ≈ [−2e25, +3e25] ≈ **5e25 m**.
- That band needs exact per-m/per-run correction (geResidueRunCellOkB, ~40m/run): ~5e25/40 ≈ **1.3e24 runs** vs ~1e6 feasible → infeasible by ~18 orders.
- Even a PERFECT 1-H-unit bracket (box_loss→0.0016, requires the per-m true-u which is itself infeasible-coverage): band {D_top>0.685} ≈ ±1e25 m → ~5e23 runs. Still infeasible.

**Root cause (measured, not estimated): the minimax deficit envelope's near-worst region is intrinsically ~1e25 mantissas wide (broad-flat peak). Proving any bound within ~0.014 ulp of the true worst requires exact treatment over ~1e24+ residue-runs.** No bracket/cell/residue technique at feasible `decide` granularity avoids this; it is set by the approximation's flatness, removable only by a different (sharper-peaked) approximation = a Solidity/algorithm change (forbidden).

**FINAL feasibility verdict at bias 0.3387:** feasibly-provable axiom-clean bound ≈ **1.70** (wide cells barely beat the proven uniform 1.7035; global LT-bound = max D_top 0.6866 + 1 + box_loss ≈ 1.7008). **1.6866 and 1.6788 are TRUE but not feasibly provable** (need ~1e24 exact runs). The 1.7035 proof remains the verified deliverable.

## LOWEST FEASIBLE BOUND at bias 0.3387 (2026-06-23, two-subagent investigation): ≈ 1.696–1.701 ulp, LT-bound

The lowest kernel-certifiable bound with FEASIBLE (tens-of-cells) certificates is set by the binding LT branch:
  **B_feasible = LT_true_worst + box_loss_LT = 1.68659 + (0.0095…0.0142) ≈ 1.696…1.701 ulp.**

Evidence:
- **LT is binding:** LT true worst 1.68659 (witness, verified) > GE true worst ~1.678. Since box_loss is symmetric across branches, the LT cell cap (1.68659+box_loss) exceeds the GE cell cap (1.6921, kernel) — so the GE route's 1.6921 is NOT the global floor; LT pins it at ~1.70.
- **box_loss_LT ≈ box_loss_GE ≈ 0.0095–0.0142:** `bracket_lt_lo` (FloorBracket.lean:2252) is a byte-for-byte structural mirror of `bracket_ge_lo` (same SLOPPc/SLOPQc, same Uc=2333e24, same PPc/QQc, same 2^104 u-floor, same homEvalI monotonicity). GE cell cap 1.6921 = GE_true_worst(~1.678) + ~0.0142 (calibrated: errGeK decodes to lnErrQ exactly, boundNum 1692115493).
- **Hybrid (wide + exact runs) buys ~0:** the deficit peak is broad-flat; band width scales like √(drop/3.6e-53), so any ≥1e-3-ulp drop needs ≥1e23 exact runs (~17 orders past the 1e6-run budget). Within budget the hybrid shaves ≤1e-20 ulp.
- **The "+1" residue is structurally unavoidable for wide cells** (it IS the high-freq phase; `directResidueGapModOkB` only works per-run, and its max saving is 7.1e-5 ulp anyway).
- **Only lever is box_loss** (0.0142→0.0095 ≈ 0.005 ulp), capped below by 1+D_top_peak = 1.6866 (reachable only per-m = infeasible).

**State of the build:** deployed proof uses uniform-residue for BOTH branches at cap 7035 = 1.7035 (ErrorBoundCert lnErrorBoundNum=1703500000). The GE factored cell route (FactoredCap + ErrCertGe*) is BUILT but NOT wired (referenced nowhere outside its files). The LT error-bound cell route is NOT built: missing `lt_x1_cap_d22`/`lt_pos_cut_reduced` (mirror FactoredCap, using the existing `x1capLtUp`/`bracket_lt_lo`/`posPhaseNatLt`/`posAvailLt`), `certErrLt`/`errLtK(=errGeK)`/`errLtW(=errGeW)`, and an `ErrCertLt*` cell cover (~15 cells, per the existing `ltLo_nonneg` 15-cell floor cover). errLtK/errLtW are branch-INDEPENDENT (= the GE values); only ltTN2b/ltTD2b differ.

**To DELIVER the ~1.70 floor:** wire GE factored route + build the LT mirror + cascade lnErrorBoundNum to the LT-binding value (~1.696–1.701e9, bisect to pin exactly) + recheck neg (6785<7000 ✓). A few hundred lines of mechanical mirroring + one cert-regen pass. Gain over deployed 1.7035: ~0.003–0.007 ulp (marginal).

## LOWEST BIAS MARGIN + LOWEST FEASIBLE BOUND FROM IT (2026-06-23, measured, trusted-model-verified)

Two-subagent investigation + trusted-Lean-model (`accOf`=pre-floor r_4, bracket evalPoly) + bc verification. All witnesses cross-checked in the kernel model.

**Deployed (margin 0.3386591):** true worst W = **1.68690 ulp** (witness x=2733040867674376939742808330485465350143, r=49359701813120862664282891977, verified). Over-estimate headroom H_true = min D = **0.01005186 ulp** (witness m=40241540922992177420755586228, k=0, acc=115311527063840171942218493471217128169256224183100, verified). Both peaks LT branch.

**Lowest TRUE margin (function still never-overshoots, min D=0):** M_min_true = 0.3386591 − 0.01005 = **0.328607 ulp** (BIAS 116873961749927929127912020551562066833967533774462). At it, true worst W_true(M_min_true) = **1.67678 ulp** (= range(D) 0.67689 + ~1 phase; W drops ~1:1 with margin). Note 1.67678 < 1.6788, so 1.6788 is TRUE only at ~this margin.

**Lowest PROVABLE margin — the killer:** the never-overshoot proof binds at the over-estimate peak using the LT LOWER bracket of |H| (acc=−K|H|+…, bound acc up ⇒ |H| down). Measured `ns_slop = slop_lo(over-est peak) = 5.69 H-units = 0.00899 ulp`, vs headroom 0.01005 ⇒ proof slack only **0.00106 ulp**. So the margin can be lowered PROVABLY by at most ~0.001 (to ~0.3376), NOT to M_min_true. (Nearby m have slop_lo up to ~6.4 H-units capped at D, so the true provable reduction ≤ 0.00106 and may be ~0.) **The deployed 0.3387 is essentially already the minimal provable margin.** (This MEASURED result corrects the stale-doc "minimal-provable 0.330".)

**Lowest feasibly-proven bound:** B_min = W_true(M_min_prov) + box_loss. With M_min_prov ≈ 0.3376–0.3387 ⇒ W_true ≈ 1.6858–1.6869; box_loss (LT upper-bracket, error-bound) = 0.00937 ulp per-m at the under-est worst, ≈0.0142 ulp as a wide-cell cover max. So **B_min ≈ 1.696 (per-m best) to 1.700 (cell)**. Barely below the deployed/proven 1.7035.

**CONCLUSION:** lowering the bias margin does NOT meaningfully help. The never-overshoot bracket slop (~0.009 ulp) nearly equals the over-estimate headroom (~0.010 ulp), so the provable margin can't drop more than ~0.001; and even at the true minimum margin (0.3286, NOT provable with the current never-overshoot bracket) the floor is W_true 1.6768 + box_loss 0.0142 = ~1.691. The absolute lowest feasibly-proven error bound at any provable margin ≈ **1.696–1.700 ulp**; the deployed 1.7035 is within ~0.004 of it. To go materially lower (~1.69) one would need BOTH a tighter never-overshoot bracket (to make M_min_true provable) AND the error-bound cell route — and even then only ~1.691.

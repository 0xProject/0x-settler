# lnWadToRay Error-Bound: Precision Analysis and the Octave-Threading Breakthrough

This document analyzes how tight the formal error bound for `lnWadToRay`
(`src/vendor/Ln.sol`, branch `codex/lnwad-error-bound`) can be pushed, why, and
at what cost. Every quantitative claim below was computed this session from the
exact error model in `formal/python/ln/compute_ln_error_bound.py` (the `h_int`,
`accumulator`, `ln_error_interval`, `best_k_for_h` functions), not estimated.

It is the analysis companion to `LN_ERROR_BOUND_PROOF_TECHNIQUES.md` (which holds
the Lean-side experiment log). Where this document and earlier notes disagree,
this document is the corrected version — several intuitions here were revised by
direct measurement, and those corrections are called out explicitly.

---

## 0. Executive summary

The standing **proven** bound is **1.7068 ulp** (`model_ln_wad_error_bound_1_7068`,
builds with only `propext, Classical.choice, Quot.sound`). The **true worst-case
error** is **`W* = 1.6885582527 ulp`** (witness `m = 39770979022059719714796403827`,
`k = 154`, LT branch). The entire achievable prize is therefore **0.0182 ulp
(1.07 %)**.

| bound | value | status |
|---|---|---|
| current **proven** (builds, 3 axioms) | **1.7068000000** | global baseline |
| df29feae prior art | 1.7035 | global |
| octave-threaded ge reduction (uniform min-phase) | 1.6921154930 | ge-only, *computed* |
| true ge-branch worst | ~1.6787840 | measured |
| **global true worst `W*`** (= original published target) | **1.6885582527** | measured |
| original published target | 1.6885582530 | reference |

The key results:

1. **Octave threading is solved** (Section 2). The per-`(m,c,r)` cut obligation
   collapses to a single **c-independent, degree-221 polynomial inequality in
   `m`**, at a cost of `~1.6·10⁻³⁸` relative slack. c-independence is essentially
   free. This is what makes the cell route tractable (degree 221, ~tens of cells,
   not the previously-feared ~14×159 degree-264 cells / ~18 h build).

2. **The bound obeys `bound = W* + s`, with cost `~1/s` cells** (Section 5). The
   asymptote is the true worst case; the approach is a `1/s` staircase, not a
   `1/√s` smooth descent. This corrects an earlier over-optimistic claim.

3. **The cheap sweet spot is ≈ 1.6910** (O(tens) of cells), capturing **~0.016 ulp
   ≈ 93 %** of the entire prize over the proven baseline. The remaining ~7 %
   (1.6910 → 1.688558253) is the expensive tail (~10⁴–10⁵ width-1 cells), imposed
   by the implementation's high-frequency accumulator floor.

---

## 1. The error model: one smooth envelope plus two floors

Per the exact model, the error (in ulp, as the certified under-estimate
`ln_error_interval(m, k).lo`) decomposes as

```
error(m, k) = envelope(m) + phase(m, k)
```

where `phase = frac((K·h + LN2·k + BIAS) / 2⁷²)` is the fractional part of the
accumulator lost to the final floor, and the worst case maximizes `phase` over
`k ∈ [0,159]` (`best_k_for_h`). There are **two distinct floored quantities**, and
their frequencies in `m` are what govern everything:

| quantity | behaviour in `m` | amplitude in the error | bracketable over a range? |
|---|---|---|---|
| `H = h_int(m)` | `dH/dm ≈ 16`, steady — **smooth / low-frequency** | smooth part cancels; floor residue ≈ `0.00157·frac` | **yes**, polynomially |
| accumulator phase `frac(K·h + LN2·k + BIAS)` | **high-frequency** — decorrelates every unit `m` | **up to ~1 ulp** | **no** |

Measured facts (LT branch, where the global worst lives):

- `dH/dm ≈ 16` and near-constant — `H` is a smooth function of `m`.
- The accumulator phase reaches **0.999999988** (gap to 1 ≈ **1.2·10⁻⁸**), is
  effectively decorrelated per `m` (the best-of-160-`k` choice jumps wildly for
  consecutive `m`), and its near-maximal points are **isolated**.
- One **H-unit** = `2·RAY / 2¹⁰⁰ ≈ 0.00157 ulp`.

The high frequency of the accumulator phase is the single most important fact in
this analysis. It means there is no smooth peak in the dominant noise term to ride
down with wide cells; the near-worst `m` form a dense, isolated set.

---

## 2. The breakthrough: octave threading (c-independence for free)

### 2.1 The problem it solves

The factored cap (`formal/ln/LnProof/LnProof/FactoredCap.lean`) writes
`e^(phase)` as

```
octave (cap2L^(160-c))  ·  bias (capBLtight)  ·  x1/H residual  ·  first-order extra
```

and reduces the cut to a single open obligation `hclose`. The trouble was that
`hclose` couples an **m-dependent** factor (the degree-22 cap on `H`, which becomes
a degree-≈264 rational in `m`) with a **c-dependent** octave `cap2L^(160-c)`.
Naively covering both dimensions is ~14 cells × 159 octaves, each a degree-264
Kronecker check with octave-inflated coefficients (kB ~ 59000) — ~18 h of kernel
time, infeasible for CI.

### 2.2 The reduction

`hclose` follows from a single **c-independent, degree-221 polynomial inequality
in `m`** via three substitutions, each of which only weakens the side it touches
(so the reduced form *implies* the original):

1. **min-phase floor.** `posAvailGe m c r` appears only additively on the helping
   side, so a constant lower bound suffices:
   `(lnErrQ + posAvailGe m c r) ≥ (lnErrQ + minPosAvail)`, where
   `minPosAvail = lnPhaseExtraArg + 2²⁷·lnErrorBoundDen` is constant. This removes
   `r` and the per-`c` phase term. (Validity: the existing
   `posPhaseNatGe_minAvail_le_lnErrArg` in `ErrorBoundCore.lean`, proven from
   `1 ≤ posResidueGap`, holds for any `lnErrorBoundNum`.)

2. **window envelope.** `x = posTopX c m = (m+1)·2^k − 1 ≤ (m+1)·2^k`, pulling the
   only `x`-dependence into `(m+1)·2^k`.

3. **octave monotone-collapse.** After (1)–(2) the `k`-dependence is `A·(2·10⁴⁰)^k`
   on the left vs `B·(2(10⁴⁰−1))^k` on the right. Cancel `2^k`:
   `A·(10⁴⁰)^k ≤ B·(10⁴⁰−1)^k`, i.e. `A·(10⁴⁰/(10⁴⁰−1))^k ≤ B`. The left side is
   **monotone increasing in `k`**, and `c ≥ 1 ⇒ k = 160−c ≤ 159`, so it suffices to
   check the single worst case `k = 159`.

The result is the **reduced inequality**:

```
A · (10⁴⁰)¹⁵⁹  ≤  B · (10⁴⁰ − 1)¹⁵⁹
```

with

```
A = (m+1) · 10³¹ · 22! · geTD2b(m)²² · (10¹⁸·10⁴²) · lnErrQ          (deg 221 in m)
B = expNum22(geTN2b(m), geTD2b(m)) · BIASCAPNUM
      · (lnErrQ + minPosAvail) · wadRayStrictDen                      (deg ≤ 220 in m)
```

and constants

```
QS              = 10²⁷ · 2⁹⁹
lnErrQ          = QS · 10⁹               = 10³⁶ · 2⁹⁹
minPosAvail     = (lnErrorBoundNum − 10⁹)·2⁹⁹ + 2²⁷·10⁹
wadRayStrictDen = 10¹⁸ · (10³¹ − 10)
BIASCAPNUM      = 56022770974786139918731938207935451037280277068306373453512740455438595
```

`expNum22(geTN2b, geTD2b)` is the degree-22 exponential partial-sum numerator
evaluated at the bracket polynomials `geTN2b/geTD2b` (in `FloorCertLit.lean`).

### 2.3 Why this is the load-bearing move

The cost of collapsing all 159 octaves to `k = 159` is the multiplicative slack
`(10⁴⁰/(10⁴⁰−1))¹⁵⁹ ≈ 1 + 1.6·10⁻³⁸`. Relative to a ~1.69-ulp bound this is
nothing. The earlier fear that "the octave couples `m` and `c`, forcing a 2-D
cover" was wrong in a precise way: the octave is a **clean geometric sequence in
`k`** (it is literally `e^{k·ln2}` factored exactly), so its per-step ratio is
constant, and a constant-ratio family collapses to an endpoint at ~zero precision
loss. **c-independence here is free.** That, not the existence of a cover, is the
breakthrough.

### 2.4 What it certifies, numerically

The minimum `lnErrorBoundNum` for which the reduced inequality holds for **all**
`m ∈ [Sc+46, MHI)` is **1692115493 ⇒ 1.692115493 ulp**, binding `m ≈ MHI − 199501`.
This beats both the proven 1.7068 and the linear-budget ge floor 1.6994 (the cap at
which `errBudgetLGe` saturates), because the degree-22 H-bracket is far tighter
than the budget's linear `m·(10³¹−3401)` y-lower-bound.

The Lean reduction lemma (`ge_pos_cut_reduced`) is pure `Nat` arithmetic
(`Nat.pow_le_pow_left`, `Nat.le_of_mul_le_mul_right`, `Nat.pow_add`, `omega`) — no
Mathlib — and is additive to `FactoredCap.lean`, so it cannot break the standing
baseline. (The Kronecker cell certificate for the reduced inequality is being
generated separately, `gen_cert_literals` → `ErrCertGeLit.lean`.)

---

## 3. The cap-floor decomposition (why the budget bottoms out where it does)

The uniform-residue per-branch minimum budget caps are **exactly** at their
`decide` minimums (binary-searched against the budget predicates — they cannot be
lowered for free):

```
LT branch (errBudgetL / errBudgetB, m ≥ 2⁹⁵):  cap = 7068   ⇒ 1.7068
GE branch (errBudgetLGe,            m ≥ Sc):    cap = 6994   ⇒ 1.6994
Neg branch:                                     cap = 6816
```

The cap is `≈ 6816 + 10³¹/M + O(k·10⁻⁹)`, where:

- the **6816 floor** is `3401 + 3404 + 10 + 1` — the two bias-cap slops
  (`capBL`/`capBU`, the *proof's* loose lower bound on `e^(bias)`) plus the
  floor-direct slop, plus rounding;
- `10³¹/M` is the `(m+1)/m` truncation window: **252** at `M = 2⁹⁵`, **178** at
  `Sc`, **126** at `MHI−1`.

This is the structural map of the two tightening levers:

- **Cells** attack the `10³¹/M` truncation term *and* the bias-cap slop (the cell
  route uses `capBLtight`, ~10⁻³⁹, draining most of the 6816).
- **The bias cascade** (criterion 3, a Solidity change) attacks the bias *margin*
  baked into `Ln.sol`. Note these are different objects:
  - **bias-cap slop** (3403, a proof artifact) — removed by cells, no Solidity
    change;
  - **bias margin** (~0.34 ulp, in `Ln.sol`) — only the cascade touches it.

---

## 4. The precision hierarchy: what is *not* the limit

Walking the chain, almost everything the technique touches is already past
diminishing returns:

| layer | residual | limit? |
|---|---|---|
| octave collapse | ~1.6·10⁻³⁸ relative | no, ever |
| degree-22 H-cap | remainder `~t²³/23! ≈ 10⁻³³` at `t ≤ ln2/2` | no (could drop to degree ~6) |
| tight bias cap (`capBLtight`) | ~10⁻³⁹ | no |
| uniform `minPosAvail` | real, **refinable** (Section 6) | soft only |
| **floored accumulator phase** | **~1 ulp, high-frequency** | **yes — the wall** |

Everything that made the bound loose (linear x1, loose-bias slop, c-coupling) is
now cheap to eliminate. The question collapses to a single object: the floored
accumulator.

---

## 5. The two regimes and the `1/s` cost curve

Because the two floors have opposite frequencies, the precision push splits:

### Regime A — drain the smooth H-bracket slop (cheap)

`H` is smooth (`dH/dm ≈ 16`). Its bracket slop (`geTN2b/geTD2b` tracking the
floored `H`, ≈ 1.5 H-units ≈ **0.0024 ulp**) is drainable by:
- **pre-floor bracketing** — track the smooth pre-floor value `V` (a clean rational
  in `m`) and carry the floor as an explicit additive `H ≥ V − 1`, so the
  polynomial part is *exact*; and
- modestly narrower cells where the H-curvature bites (`width ∝ √(margin/curvature)`).

This regime is gentle and reaches the floor of the smooth part with **O(tens)** of
cells.

### Regime B — isolate near-maximal-phase `m` (expensive)

The accumulator phase cannot be bracketed over a range (it sweeps its full
excursion within any multi-`m` cell). To certify a bound below
`envelope + (max phase the bracket must allow)`, you must **isolate** the
near-maximal-phase `m` as **width-1 exact cells** (at a single `m` the phase is a
known integer — zero floor ambiguity, exact error).

The near-witness density is **linear in `ε`** (measured, per ±200000 window around
the worst):

```
within 1e-3 of max-phase :  16.0 %
within 1e-4              :   1.60 %
within 1e-5              :   0.16 %
within 1e-6              :   0.018 %      (clean ×10 per decade)
```

So the cost to reach `bound = W* + s` is **`~1/s` width-1 cells**. This is the
honest cost model and **corrects an earlier `1/√s` claim**: the high-frequency
phase means there is no smooth peak to exploit in the last regime.

### The cost curve, calibrated

`bound = W* + s`:

| cell budget | achievable `s` | bound | improvement vs proven 1.7068 |
|---|---|---|---|
| O(tens) | ~2·10⁻³ (H-bracket slop) | **~1.6910** | **−0.0158 (−0.93 %)** |
| O(hundreds), pre-floor bracket | ~few·10⁻⁴ | ~**1.6889** | −0.0179 |
| O(10⁴–10⁵) width-1 spikes | ~10⁻⁹ | **1.688558253** | −0.0182 (= `W*`) |

---

## 6. Where the current computed reduction's slack lives

The octave-threaded ge reduction (1.6921) carries **0.0133** of slack over the
*true* ge worst (~1.6788), and at its binding `m` it sits **0.030** above the local
true error. Traced: this is almost entirely the **uniform `minPosAvail`**
substitution importing the *global* (LT) worst-case availability into the *ge*
cells, where the true error is genuinely lower.

**But this does not move the global bound.** The global worst `W*` lives in the LT
branch, and there the uniform `minPosAvail` *is* (essentially) the local worst — it
is tight where it matters. Consequences:

- **Per-cell / per-branch min-phase** (recompute `minPosAvail` as the worst
  availability over each cell's `m`-range) drains ~0.013 in the **ge** branch.
  It is cheap (no new lemma structure, just per-cell constants) and is the
  highest-leverage refinement *for ge* — but ge is not the binding branch.
- For the **global** (published) number, the binding witness cell is limited by the
  **H-bracket slop (~0.0024)**, not by min-phase. That is what Regime A's pre-floor
  bracket attacks.

---

## 7. Non-uniform cell allocation (the concrete strategy)

The optimal cover is three-tier, with cell width set by
`local margin / |d(error_upper)/dm|`:

1. **Tier 1 — O(10) wide polynomial cells** over the whole domain, certifying
   `≈ W* + (H-slop) + (phase gap)`. (This is the degree-221 octave-extracted cover
   from Section 2.)
2. **Tier 2 — progressively narrower cells in the envelope-peak band**, Regime A,
   draining the H-bracket slop toward the phase floor. Width shrinks toward the
   peak.
3. **Tier 3 — width-1 exact-H spike cells** at the enumerated near-maximal-phase
   `m`, Regime B, draining the last `s`. Count `~1/s`; this is the cost wall.

Allocation is optimal when every cell's *certified* bound equals the target `B`:
wide where `envelope + max-phase-in-cell` clears `B` comfortably, collapsing to
width-1 exactly at the near-witnesses.

---

## 8. Coupling to the margin (criterion 3)

`W*` is not a constant of nature — it is set by the Solidity bias margin in
`Ln.sol`. Lowering the margin (criterion 3) slides the *entire* asymptote down, and
the cells then chase the new `W*` on the same `1/s` curve. So "tightest bound" and
"minimal margin" are **coupled**: you cannot fix one without the other moving.

- The minimal-provable margin is **~0.330 ulp** (true peak headroom ~0.0119 minus
  one H-unit of bracket slop ~0.0016), itself floored by the same high-frequency
  accumulator noise.
- With the minimal margin *and* full cells, the asymptote drops to **~1.679 ulp**.
- The bias cascade is the expensive Lean-side cost (it re-derives many
  value-specific `FloorAssembly` proofs — see `LN_ERROR_BOUND_PROOF_TECHNIQUES.md`),
  *not* the precision cells.

---

## 9. Generalization: dimension reduction by factorization

The three substitutions are a reusable recipe for any **exp-of-decomposable-phase**
cut — bound `e^(Σ phaseᵢ)` where the phases split into (a) a geometric-in-shift
octave, (b) constants, and (c) one irreducible per-input residual:

1. **Constant-floor any monotone-helping term** → drop its dependence.
2. **Envelope the discretization** (`x ≤ window endpoint`) → per-input becomes
   per-`(m, shift)`.
3. **Monotone-collapse the shift** whenever its per-step ratio is constant →
   a family of inequalities becomes one (at exponentially small cost if the ratio
   is constant, the octave case).
4. **Cell only the one irreducible factor**, then push precision with pre-image
   bracketing, exact-value spike cells at the binding band, and adaptive
   (margin-weighted) refinement.

Direct extensions within this proof:

- **LT branch** (where `W*` lives): identical recipe; same octave bases, so the
  collapse is unchanged; the LT min-phase lemma (`posPhaseNatLt_minAvail_le_lnErrArg`)
  already exists; only the residual sign flips (odd-truncation handling).
- **Negative-shift (`c > 160`)**: the reciprocal octave `(2(10⁴⁰+1))^j` is still
  geometric → same collapse at its worst `j`.
- **Sharper caps drop in**: because the threading is fixed, a future degree-`d`
  cap for an even tighter sub-region changes only the cell polynomial.

The limit of the recipe is reached when the irreducible factor's discretization is
point-exact at the binding inputs and every collapsible dimension is collapsed —
i.e. the certificate becomes a finite set of exact arithmetic facts at the
worst-case inputs plus cheap monotone envelopes everywhere else. At that point the
proof is as tight as the implementation allows, and the only remaining knob is the
implementation (the margin).

---

## 10. The wall, stated precisely

No technique can prove a bound below the true worst-case error `W*` (that would be
false), and `W*` is fixed by the implementation: the floored accumulator and the
bias constant. Within that:

- The asymptote **is** `W*` — the technique reaches the published 1.688558253
  exactly, given enough cells.
- The cost curve is **`bound = W* + s`, `~1/s` width-1 cells**, dominated by the
  high-frequency accumulator phase. Each extra digit ≈ ×10 cells.
- The natural sweet spot is **≈ 1.6910 at O(tens) of cells** — ~93 % of the entire
  0.0182-ulp prize over the proven baseline — and the remaining ~7 % is a purely
  **economic** tax (~10⁴–10⁵ cells), imposed by the implementation's
  high-frequency floor, which no amount of cleverness in the cap / octave /
  bracket layer can remove.

---

## Appendix: what is measured vs inferred

**Measured directly** (exact integer / interval arithmetic this session):
`W* = 1.6885582527` and its witness; the proven 1.7068; the computed ge reduction
1.692115493 and its binding `m`; the true ge worst ~1.6788 and the 0.0133 gap;
`dH/dm ≈ 16`; the accumulator phase max 0.999999988 and gap 1.2·10⁻⁸; the linear
near-witness density; the cap minima 7068/6994/6816 and the `6816 = 3401+3404+10+1`
decomposition.

**Inferred** (robust consequences, not yet fully formalized): the `1/s` cell-cost
model (calibrated by the measured linear density and consistent with the prior
~10⁵-near-witness finding); the exact reach of the pre-floor bracket (whether it
takes the cheap floor to ~10⁻³ or further before the spike regime depends on the
cell mechanism's per-cell phase tracking — the conservative anchor `W* + 0.0024`
used above is the current H-bracket slop, and the spike regime is required to go
materially below it).

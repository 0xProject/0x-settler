# Formal Verification of Sqrt.sol

Machine-checked proof that `Sqrt.sol:_sqrt` converges to within 1 ULP of the true integer square root for all uint256 inputs, and that the floor-correction step in `sqrt` yields exactly `isqrt(x)`.

## What is proved

For all `x < 2^256`, the Lean development proves:

1. **`innerSqrt x` is within 1 ULP of a canonical integer-sqrt witness**  
   (`m ≤ innerSqrt x ≤ m+1` with `m := natSqrt x`), via `innerSqrt_bracket_u256_all`.
2. **`floorSqrt x` satisfies the integer-sqrt spec**  
   (`r^2 ≤ x < (r+1)^2`), via `floorSqrt_correct_u256`.

"Proved" means: Lean 4 type-checks the theorems with zero `sorry` and no axioms beyond the Lean kernel.

## Proof structure

```
FloorBound.lean          Lemma 1 (floor bound) + Lemma 2 (absorbing set)
    |
StepMono.lean            Step monotonicity for overestimates
    |
BridgeLemmas.lean        One-step error recurrence bridge
    |
FiniteCert.lean          256-case finite certificate (native_decide)
    |
CertifiedChain.lean      6-step certified error chain
    |
SqrtCorrect.lean         Definitions + octave wiring + end-to-end theorems
```

### Lemma 1 -- Floor Bound (`babylon_step_floor_bound`)

> For any `m` with `m*m <= x` and `z > 0`: `m <= (z + x/z) / 2`.

A single truncated Babylonian step never undershoots `isqrt(x)`. Proved algebraically via two decomposition identities (`(a+b)^2 = b(2a+b) + a^2` and `(a+b)(a-b) + b^2 = a^2`) which reduce the nonlinear AM-GM core to linear arithmetic.

### Lemma 2 -- Absorbing Set (`babylon_from_ceil`, `babylon_from_floor`)

> Once `z` is in `{isqrt(x), isqrt(x)+1}`, it stays there under further Babylonian steps.

### Step Monotonicity (`babylonStep_mono_z`)

> For `z1 <= z2` with `z1^2 > x`: `step(x, z1) <= step(x, z2)`.

This justifies the "max-propagation" upper-bound strategy: computing 6 steps at `x_max = 2^(n+1) - 1` gives a valid upper bound on `_sqrt(x)` for all `x` in the octave.

### Finite Certificate Layer (`FiniteCert`, `CertifiedChain`)

`FiniteCert.lean` contains precomputed `(lo, hi)` octave bounds and the recurrence constants
`d1..d6`. `native_decide` proves the full 256-case certificate:

- `d1 ≤ lo`
- `d2 ≤ lo`
- `d3 ≤ lo`
- `d4 ≤ lo`
- `d5 ≤ lo`
- `d6 ≤ 1`

`CertifiedChain.lean` then lifts this finite certificate to runtime variables (`x`, `m`) and proves `run6From x seed ≤ m + 1` under the octave assumptions.

### Floor Correction (`floor_correction`)

> Given `z > 0` with `(z-1)^2 <= x < (z+1)^2`, the correction `if x/z < z then z-1 else z` yields `r` with `r^2 <= x < (r+1)^2`.

## Prerequisites

- [elan](https://github.com/leanprover/elan) (Lean version manager)
- Lean 4.28.0 (installed automatically by elan from `lean-toolchain`)

No Mathlib or other dependencies.

## Building

```bash
cd formal/sqrt/SqrtProof
lake build
```

## Python verification script

`verify_sqrt.py` is a standalone Python script (requires `mpmath`) that independently verifies the convergence bounds using interval arithmetic. It served as the prototype for the Lean proof.

```bash
pip install mpmath
python3 verify_sqrt.py
```

## File inventory

| File | Lines | Description |
|------|-------|-------------|
| `SqrtProof/FloorBound.lean` | 136 | Lemma 1 (floor bound) + Lemma 2 (absorbing set) |
| `SqrtProof/StepMono.lean` | 82 | Step monotonicity for overestimates |
| `SqrtProof/BridgeLemmas.lean` | 178 | Bridge lemmas for one-step error contraction |
| `SqrtProof/FiniteCert.lean` | 618 | 256-case finite certificate tables + `native_decide` proofs |
| `SqrtProof/CertifiedChain.lean` | 133 | Multi-step certified chain (`run6_le_m_plus_one`) |
| `SqrtProof/SqrtCorrect.lean` | 379 | Definitions, octave wiring, theorem wrappers |
| `verify_sqrt.py` | 396 | Python prototype of convergence analysis |

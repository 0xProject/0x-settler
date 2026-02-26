# Formal Verification of Sqrt.sol

Machine-checked proof that `Sqrt.sol:_sqrt` converges to within 1 ULP of the true integer square root for all uint256 inputs, and that the floor-correction step in `sqrt` yields exactly `isqrt(x)`.

## What is proved

For all `x < 2^256`:

1. **`_sqrt(x)` returns `isqrt(x)` or `isqrt(x) + 1`** (the inner Newton-Raphson loop converges after 6 iterations from the alternating-endpoint seed).

2. **`sqrt(x)` returns exactly `isqrt(x)`** (the correction `z := sub(z, lt(div(x, z), z))` is correct).

"Proved" means: Lean 4 type-checks the theorems with zero `sorry` and no axioms beyond the Lean kernel.

## Proof structure

```
FloorBound.lean          Lemma 1 (floor bound) + Lemma 2 (absorbing set)
    |
StepMono.lean            Step monotonicity for overestimates
    |
SqrtCorrect.lean         Definitions, computational verification, main theorems
```

### Lemma 1 -- Floor Bound (`babylon_step_floor_bound`)

> For any `m` with `m*m <= x` and `z > 0`: `m <= (z + x/z) / 2`.

A single truncated Babylonian step never undershoots `isqrt(x)`. Proved algebraically via two decomposition identities (`(a+b)^2 = b(2a+b) + a^2` and `(a+b)(a-b) + b^2 = a^2`) which reduce the nonlinear AM-GM core to linear arithmetic.

### Lemma 2 -- Absorbing Set (`babylon_from_ceil`, `babylon_from_floor`)

> Once `z` is in `{isqrt(x), isqrt(x)+1}`, it stays there under further Babylonian steps.

### Step Monotonicity (`babylonStep_mono_z`)

> For `z1 <= z2` with `z1^2 > x`: `step(x, z1) <= step(x, z2)`.

This justifies the "max-propagation" upper-bound strategy: computing 6 steps at `x_max = 2^(n+1) - 1` gives a valid upper bound on `_sqrt(x)` for all `x` in the octave.

### Computational Verification (`all_octaves_pass`)

> For each of the 256 octaves (bit-widths 1-256), the max-propagation result satisfies `(z-1)^2 <= x_max`.

Proved by `native_decide`, which compiles the 256-case check to GMP-backed native code. This is the convergence proof: it shows 6 iterations suffice for all uint256 inputs.

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
| `SqrtProof/SqrtCorrect.lean` | 200 | Definitions, `native_decide` verification, main theorems |
| `verify_sqrt.py` | 250 | Python prototype of convergence analysis |

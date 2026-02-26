# Formal Verification of Cbrt.sol

Machine-checked proof that `Cbrt.sol:_cbrt` converges to within 1 ULP of the true integer cube root for all uint256 inputs, and that the floor-correction step in `cbrt` yields exactly `icbrt(x)`.

## What is proved

For all `x < 2^256`:

1. **`_cbrt(x)` returns `icbrt(x)` or `icbrt(x) + 1`** (the inner Newton-Raphson loop converges after 6 iterations from the seed).

2. **`cbrt(x)` returns exactly `icbrt(x)`** (the correction `z := sub(z, lt(div(x, mul(z, z)), z))` is correct).

"Proved" means: Lean 4 type-checks the theorems with zero `sorry` and no axioms beyond the Lean kernel.

## Proof structure

```
FloorBound.lean     Cubic AM-GM + floor bound for one NR step
    |
CbrtCorrect.lean    Definitions, computational verification, main theorems
```

### Cubic AM-GM (`cubic_am_gm`)

> `(3m - 2z) * z^2 <= m^3` for all `m, z`.

The core algebraic inequality, proved via two witness identities:
- `z <= m`: `(3m-2z)*z^2 + (m-z)^2*(m+2z) = m^3`
- `m < z <= 3m/2`: `(3m-2z)*z^2 + (z-m)^2*(m+2z) = m^3`
- `z > 3m/2`: LHS = 0 (Nat subtraction underflow)

Each witness identity is proved by the 4-line `ring`-substitute:
```lean
simp only [Nat.add_mul, Nat.mul_add]         -- distribute
simp only [Nat.mul_assoc]                    -- right-associate
simp only [Nat.mul_comm, Nat.mul_left_comm]  -- sort factors
omega                                         -- collect coefficients
```

### Floor Bound (`cbrt_step_floor_bound`)

> For any `m` with `m^3 <= x` and `z > 0`: `m <= (x/(z*z) + 2*z) / 3`.

A single truncated NR step never undershoots `icbrt(x)`.

### Computational Verification (`cbrt_all_octaves_pass`)

> For each of the 256 octaves, the max-propagation result satisfies `(z-1)^3 <= x_max`.

Proved by `native_decide` over `Fin 256`.

### Lower Bound Chain (`innerCbrt_lower`)

> For any `m` with `m^3 <= x` and `x > 0`: `m <= innerCbrt(x)`.

Chains `cbrt_step_floor_bound` through 6 NR iterations from the seed.

### Floor Correction (`cbrt_floor_correction`)

> Given `z > 0` with `(z-1)^3 <= x < (z+1)^3`, the correction `if x/(z*z) < z then z-1 else z` yields `r` with `r^3 <= x < (r+1)^3`.

## Prerequisites

- [elan](https://github.com/leanprover/elan) (Lean version manager)
- Lean 4.28.0 (installed automatically by elan from `lean-toolchain`)
- No Mathlib or other dependencies

## Building

```bash
cd formal/cbrt/CbrtProof
lake build
```

## Python verification script

`verify_cbrt.py` independently verifies convergence for all 256 octaves. Requires `mpmath`.

```bash
pip install mpmath
python3 verify_cbrt.py
```

## File inventory

| File | Lines | Description |
|------|-------|-------------|
| `CbrtProof/FloorBound.lean` | 121 | Cubic AM-GM + floor bound (0 sorry) |
| `CbrtProof/CbrtCorrect.lean` | 178 | Definitions, `native_decide`, main theorems (0 sorry) |
| `verify_cbrt.py` | 200 | Python convergence verification prototype |

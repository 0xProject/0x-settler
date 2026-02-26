# Formal Verification of Cbrt.sol

Machine-checked Lean development for core `cbrt` arithmetic lemmas, a reference `icbrt` function, and named correctness theorems for `_cbrt` / `cbrt` under an explicit upper-bound hypothesis.

## What is proved

1. **Reference integer cube root is formalized**:
   - `icbrt(x)^3 <= x < (icbrt(x)+1)^3`
   - any `r` satisfying those bounds is equal to `icbrt(x)`.
2. **Lower-bound chain for `_cbrt`**:
   - for any `m` with `m^3 <= x`, `m <= innerCbrt(x)`.
3. **Floor-correction lemma is formalized**:
   - if `z > 0` and `(z-1)^3 <= x < (z+1)^3`, correction returns `r` with
     `r^3 <= x < (r+1)^3`.
4. **Named end-to-end statements are present with explicit assumption**:
   - `innerCbrt_correct_of_upper`
   - `floorCbrt_correct_of_upper`
   both assume the remaining link `innerCbrt x <= icbrt x + 1`.

"Proved" means: Lean 4 type-checks these theorems with zero `sorry` and no axioms beyond the Lean kernel.

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
# Explicitly build the main proof module:
lake build CbrtProof.CbrtCorrect
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
| `CbrtProof/CbrtCorrect.lean` | ~375 | Definitions, reference `icbrt`, `native_decide` checks, and correctness theorems (0 sorry) |
| `verify_cbrt.py` | 200 | Python convergence verification prototype |

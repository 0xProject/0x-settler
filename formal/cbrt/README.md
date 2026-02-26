# Formal Verification of Cbrt.sol

Machine-checked proof that the cube root Newton-Raphson step in `Cbrt.sol` never undershoots `icbrt(x)`, via the cubic AM-GM inequality. Full convergence and correction proofs are in progress.

## What is proved

**Floor Bound** (`cbrt_step_floor_bound`): For any `m` with `m^3 <= x` and `z > 0`:

    m <= (x / (z * z) + 2 * z) / 3

A single truncated Newton-Raphson step for cube root never goes below `icbrt(x)`. This is the cubic analog of the square root floor bound.

The proof rests on the **cubic AM-GM inequality**:

    (3m - 2z) * z^2 <= m^3    for all m, z >= 0

which holds because `m^3 - (3m - 2z) * z^2 = (m - z)^2 * (m + 2z) >= 0`.

## What remains (TODO)

- Step monotonicity for cube root overestimates
- `native_decide` computational verification over 256 octaves
- Lower bound chain through 6 iterations
- Floor correction proof for `cbrt`
- Absorbing set lemmas (hold for `icbrt(x) >= 2`; small cases by computation)

These follow the same pattern as the sqrt proof and reuse the same techniques.

## Proof structure

```
FloorBound.lean     Cubic AM-GM + floor bound for one NR step
```

### Cubic AM-GM (`cubic_am_gm`)

> `(3m - 2z) * z^2 <= m^3` for all `m, z`.

Proved via two witness identities:
- `z <= m`: `(3m-2z)*z^2 + (m-z)^2*(m+2z) = m^3`
- `m < z <= 3m/2`: `(3m-2z)*z^2 + (z-m)^2*(m+2z) = m^3`
- `z > 3m/2`: LHS = 0 (Nat subtraction underflow)

Each witness identity is proved by expanding both sides to `d^3 + 3d^2z + 3dz^2 + z^3` using:
```lean
simp only [Nat.add_mul, Nat.mul_add]    -- distribute
simp only [Nat.mul_assoc]               -- right-associate
simp only [Nat.mul_comm, Nat.mul_left_comm]  -- sort factors
omega                                    -- collect coefficients
```

This 4-line `simp`/`omega` pattern serves as a `ring`-substitute for Nat without Mathlib.

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

`verify_cbrt.py` independently verifies convergence for all 256 octaves, the floor bound, and the absorbing set property. Requires `mpmath`.

```bash
pip install mpmath
python3 verify_cbrt.py
```

## File inventory

| File | Lines | Description |
|------|-------|-------------|
| `CbrtProof/FloorBound.lean` | 121 | Cubic AM-GM + floor bound (0 sorry) |
| `verify_cbrt.py` | 200 | Python convergence verification prototype |

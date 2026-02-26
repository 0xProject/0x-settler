# Formal Verification

Machine-checked proofs of correctness for critical math libraries in 0x Settler.

## Contents

| Directory | Target | Status |
|-----------|--------|--------|
| `sqrt/` | `src/vendor/Sqrt.sol` | Complete -- convergence + correction proved in Lean 4 |
| `cbrt/` | `src/vendor/Cbrt.sol` | Complete -- convergence + correction proved in Lean 4 |

## Approach

Proofs combine algebraic reasoning (carried out in Lean 4 without Mathlib) with computational verification (`native_decide` over all 256 bit-width octaves). This hybrid approach keeps the proof small and dependency-free while covering the full uint256 input space.

The core technique for each root function:

1. **Floor bound** (algebraic): A single truncated Newton-Raphson step never undershoots `iroot(x)`. Proved via an integer AM-GM inequality with an explicit algebraic witness.
2. **Step monotonicity** (algebraic): The NR step is non-decreasing in z for overestimates, justifying the max-propagation upper bound.
3. **Convergence** (computational): `native_decide` verifies all 256 bit-width octaves, confirming 6 iterations suffice for uint256.
4. **Correction step** (algebraic): The floor-correction logic is correct given the 1-ULP bound from steps 1-3.

## Prerequisites

- [elan](https://github.com/leanprover/elan) (Lean version manager)
- Lean 4.28.0 (installed automatically by elan from `lean-toolchain`)
- No Mathlib or other Lean dependencies
- Python 3.8+ with `mpmath` (for the verification scripts only)

## Building

```bash
# Square root proof
cd formal/sqrt/SqrtProof && lake build

# Cube root proof
cd formal/cbrt/CbrtProof && lake build
```

See each subdirectory's README for details.

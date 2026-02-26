# Formal Verification

Machine-checked proofs of correctness for critical math libraries in 0x Settler.

## Contents

| Directory | Target | Status |
|-----------|--------|--------|
| `sqrt/` | `src/vendor/Sqrt.sol` | Convergence + correction proved in Lean 4 |

## Approach

Proofs combine algebraic reasoning (carried out in Lean 4 without Mathlib) with computational verification (`native_decide` over all 256 bit-width octaves). This hybrid approach keeps the proof small and dependency-free while covering the full uint256 input space.

See each subdirectory's README for details.

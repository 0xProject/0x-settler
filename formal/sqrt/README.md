# Formal Verification of `Sqrt.sol`

This directory contains a Lean proof that the `Sqrt.sol` square-root flow is correct on the uint256 domain:

- `_sqrt(x)` lands in `{isqrt(x), isqrt(x) + 1}`
- `sqrt(x)` (floor correction applied to `_sqrt`) satisfies `r^2 <= x < (r+1)^2`

## Architecture

The proof is layered from local arithmetic lemmas to end-to-end theorems:

```
FloorBound      -> single-step floor bound + absorbing-set lemmas
StepMono        -> monotonicity of Babylonian updates on overestimates
BridgeLemmas    -> one-step error recurrence used for certification
FiniteCert      -> per-octave numeric certificate checked with native_decide
CertifiedChain  -> lifts certificate to a 6-step runtime bound
SqrtCorrect     -> EVM-style definitions + octave wiring + final theorems
```

`SqrtProof.lean` is the library root that imports the full proof surface.

## Key ideas

1. Floor bound (`babylon_step_floor_bound`):
Every truncated Babylonian step stays above any witness `m` with `m^2 <= x`.

2. Absorbing set (`babylon_from_floor`, `babylon_from_ceil`):
Once the iterate reaches `{isqrt(x), isqrt(x)+1}`, later steps cannot leave it.

3. Certified contraction:
An explicit finite certificate bounds the error across all 256 octaves after six steps.

4. Final correction:
The `if x / z < z then z - 1 else z` branch converts the 1-ULP bracket into exact floor-sqrt semantics.

## Build

```bash
cd formal/sqrt/SqrtProof
lake build
```

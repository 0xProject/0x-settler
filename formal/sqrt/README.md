# Formal Verification of `Sqrt.sol`

This directory proves that `src/vendor/Sqrt.sol` is correct on `uint256`:

- `_sqrt(x)` lands in `{isqrt(x), isqrt(x) + 1}`
- `sqrt(x)` (with the final correction branch) satisfies `r^2 <= x < (r+1)^2`
- `sqrtUp(x)` is checked against a rounding-up spec derived from `innerSqrt`

## Architecture

The proof is layered:

```
FloorBound         -> one-step floor bounds + absorbing-set lemmas
StepMono           -> monotonicity of Babylonian updates
BridgeLemmas       -> error recurrence for certified iteration
FiniteCert         -> finite per-octave certificate
CertifiedChain     -> six-step bound for all octaves
SqrtCorrect        -> `_sqrt`/`sqrt` spec and correctness theorems
GeneratedSqrtModel -> auto-generated Lean model from Solidity assembly
GeneratedSqrtSpec  -> bridge from generated model to the spec
```

`GeneratedSqrtModel.lean` defines generated models for all three Solidity functions:

- `_sqrt`: `model_sqrt_evm`, `model_sqrt`
- `sqrt`: `model_sqrt_floor_evm`, `model_sqrt_floor`
- `sqrtUp`: `model_sqrt_up_evm`, `model_sqrt_up`

`GeneratedSqrtSpec.lean` then proves:

- `model_sqrt_evm = model_sqrt` on `x < 2^256`
- `model_sqrt = innerSqrt`
- `model_sqrt_floor_evm = floorSqrt` (generated `sqrt` matches the existing spec)
- `model_sqrt_up = sqrtUpSpec` (generated `sqrtUp` normalized model matches spec)

## Verify End-to-End

Run from repo root:

```bash
# Generate Lean model from Yul IR (requires forge)
forge inspect src/wrappers/SqrtWrapper.sol:SqrtWrapper ir | \
  python3 formal/sqrt/generate_sqrt_model.py \
    --yul - \
    --output formal/sqrt/SqrtProof/SqrtProof/GeneratedSqrtModel.lean

cd formal/sqrt/SqrtProof
lake build
```

`GeneratedSqrtModel.lean` is intentionally not committed; it is regenerated for checks (including CI).

# Formal Verification of `Sqrt.sol`

This directory proves that `src/vendor/Sqrt.sol` is correct on `uint256`:

- `_sqrt(x)` lands in `{isqrt(x), isqrt(x) + 1}`
- `sqrt(x)` (with the final correction branch) satisfies `r^2 <= x < (r+1)^2`

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

`GeneratedSqrtModel.lean` defines two models extracted from the same Solidity source:

- `model_sqrt_evm`: opcode-faithful `uint256` semantics
- `model_sqrt`: normalized Nat semantics

`GeneratedSqrtSpec.lean` then proves:

- `model_sqrt_evm = model_sqrt` on `x < 2^256`
- `model_sqrt = innerSqrt`
- therefore the generated opcode-faithful model satisfies the `_sqrt` bracket theorem.

## Verify End-to-End

Run from repo root:

```bash
python3 formal/sqrt/generate_sqrt_model.py \
  --solidity src/vendor/Sqrt.sol \
  --function _sqrt \
  --output formal/sqrt/SqrtProof/SqrtProof/GeneratedSqrtModel.lean

cd formal/sqrt/SqrtProof
lake build
```

`GeneratedSqrtModel.lean` is intentionally not committed; it is regenerated for checks (including CI).

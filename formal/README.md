# Formal Verification

Machine-checked correctness proofs for root math libraries in 0x Settler.

## Scope

- `sqrt/`: proofs and model generation for `src/vendor/Sqrt.sol` (`_sqrt`, `sqrt`, `sqrtUp`)
- `cbrt/`: proofs for `src/vendor/Cbrt.sol` (`_cbrt`, `cbrt`)

## Structure

- `formal/sqrt/`
  - Layered Lean proof (`FloorBound`, `StepMono`, `BridgeLemmas`, `FiniteCert`, `CertifiedChain`, `SqrtCorrect`)
  - Solidity-to-Lean generator: `generate_sqrt_model.py`
  - Generated Lean model/spec bridge: `GeneratedSqrtModel.lean`, `GeneratedSqrtSpec.lean`
- `formal/cbrt/`
  - Lean proof modules for one-step bounds and end-to-end correctness

## Method

- Algebraic lemmas prove one-step safety and correction logic.
- Finite domain certificates cover all uint256 octaves.
- End-to-end theorems lift these pieces to full-function correctness statements.

For `sqrt`, the Solidity source is parsed into generated Lean models, and the generated models are proved equivalent to the trusted Lean specs.

## Build

```bash
# From repo root: regenerate Lean model from Solidity, then build sqrt proof
python3 formal/sqrt/generate_sqrt_model.py \
  --solidity src/vendor/Sqrt.sol \
  --output formal/sqrt/SqrtProof/SqrtProof/GeneratedSqrtModel.lean

cd formal/sqrt/SqrtProof && lake build

# Build cbrt proof
cd formal/cbrt/CbrtProof && lake build
```

See `formal/sqrt/README.md` and `formal/cbrt/README.md` for module-level details.

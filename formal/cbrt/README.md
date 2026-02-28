# Formal Verification of `Cbrt.sol`

Machine-checked Lean 4 proof that `src/vendor/Cbrt.sol` is correct on `uint256`:

- `_cbrt(x)` lands in `{icbrt(x), icbrt(x) + 1}` for every `x < 2^256`
- `cbrt(x)` (with the floor correction) satisfies `r^3 <= x < (r+1)^3`
- `cbrtUp(x)` rounds up correctly

The proof bridges from the Solidity assembly to a hand-written mathematical spec via an auto-generated Lean model, ensuring the implementation matches the verified algorithm.

"Proved" means: Lean 4 type-checks these theorems with zero `sorry` and no axioms beyond the Lean kernel.

## Architecture

The proof is layered:

```
GeneratedCbrtModel -> auto-generated Lean model from Solidity assembly
FloorBound         -> cubic AM-GM + one-step floor bound
CbrtCorrect        -> definitions, reference icbrt, lower bound chain,
                      floor correction, arithmetic bridge lemmas
FiniteCert         -> auto-generated per-octave certificate (248 octaves)
CertifiedChain     -> six-step certified error chain
Wiring             -> octave mapping + unconditional correctness theorems
GeneratedCbrtSpec  -> bridge from generated model to the spec
```

`GeneratedCbrtModel.lean` is auto-generated from `Cbrt.sol` by `generate_cbrt_model.py` and defines:

- `model_cbrt_evm`, `model_cbrt`: opcode-faithful and normalized models of `_cbrt`
- `model_cbrt_floor_evm`, `model_cbrt_floor`: models of `cbrt` (floor variant)
- `model_cbrt_up_evm`, `model_cbrt_up`: models of `cbrtUp` (ceiling variant)

`GeneratedCbrtSpec.lean` then proves:

- `model_cbrt_evm_eq_model_cbrt`: EVM model = Nat model (no uint256 overflow)
- `model_cbrt_eq_innerCbrt`: Nat model = hand-written spec
- `model_cbrt_floor_evm_correct`: EVM floor model = `icbrt x`
- `model_cbrt_up_evm_upper_bound`: EVM ceiling model gives valid upper bound

Both `GeneratedCbrtModel.lean` and `FiniteCert.lean` are intentionally not committed; they are regenerated for checks (including CI).

## Verify End-to-End

Run from repo root:

```bash
# Generate Lean model from Yul IR (requires forge)
forge inspect src/wrappers/CbrtWrapper.sol:CbrtWrapper ir | \
  python3 formal/cbrt/generate_cbrt_model.py \
    --yul - \
    --output formal/cbrt/CbrtProof/CbrtProof/GeneratedCbrtModel.lean

# Generate the finite certificate tables
python3 formal/cbrt/generate_cbrt_cert.py \
  --output formal/cbrt/CbrtProof/CbrtProof/FiniteCert.lean

# Build and verify the proof
cd formal/cbrt/CbrtProof
lake build
```

## What is proved

1. **Reference integer cube root** (`icbrt`):
   - `icbrt(x)^3 <= x < (icbrt(x)+1)^3`
   - any `r` satisfying both bounds equals `icbrt(x)` (uniqueness)

2. **Lower bound** (`innerCbrt_lower`):
   - for any `m` with `m^3 <= x` and `x > 0`: `m <= innerCbrt(x)`
   - chains `cbrt_step_floor_bound` through 6 NR iterations

3. **Upper bound** (`innerCbrt_upper_u256`):
   - for all `x` with `0 < x < 2^256`: `innerCbrt(x) <= icbrt(x) + 1`
   - uses a per-octave finite certificate with analytic d1 bound

4. **Floor correction** (`floorCbrt_correct_u256`):
   - for all `x` with `0 < x < 2^256`: `floorCbrt(x) = icbrt(x)`

5. **Full spec** (`floorCbrt_correct_u256_all`):
   - for all `x < 2^256`: `r^3 <= x < (r+1)^3` where `r = floorCbrt(x)`

6. **EVM model correctness** (`model_cbrt_floor_evm_correct`):
   - the auto-generated EVM model of `cbrt()` from `Cbrt.sol` equals `icbrt(x)`

7. **Ceiling correctness** (`model_cbrt_up_evm_is_ceil`):
   - the auto-generated EVM model of `cbrtUp()` gives the **exact** ceiling cube root:
     `(r-1)^3 < x <= r^3` for all `0 < x < 2^256`

8. **Perfect cube exactness** (`innerCbrt_on_perfect_cube`):
   - for all `m` with `0 < m` and `m^3 < 2^256`: `innerCbrt(m^3) = m`
   - key building block: on perfect cubes, Newton-Raphson with `d^2 < m` converges exactly

## Prerequisites

- [elan](https://github.com/leanprover/elan) (Lean version manager)
- Lean 4.28.0 (installed automatically by elan from `lean-toolchain`)
- Foundry (for `forge inspect` to produce Yul IR)
- Python 3 (for model and certificate generation)
- No Mathlib or other Lean dependencies

## File inventory

| File | Description |
|------|-------------|
| `CbrtProof/FloorBound.lean` | Cubic AM-GM + floor bound |
| `CbrtProof/CbrtCorrect.lean` | Definitions, reference `icbrt`, lower bound chain, floor correction, arithmetic bridge |
| `CbrtProof/FiniteCert.lean` | **Auto-generated.** Per-octave certificate tables with `decide` checks |
| `CbrtProof/CertifiedChain.lean` | Six-step certified error chain with analytic d1 bound |
| `CbrtProof/Wiring.lean` | Octave mapping + unconditional `floorCbrt_correct_u256` |
| `CbrtProof/GeneratedCbrtModel.lean` | **Auto-generated.** EVM + Nat models of `_cbrt`, `cbrt`, `cbrtUp` |
| `CbrtProof/GeneratedCbrtSpec.lean` | Bridge: generated model ↔ hand-written spec |
| `generate_cbrt_model.py` | Generates `GeneratedCbrtModel.lean` from Yul IR |
| `generate_cbrt_cert.py` | Generates `FiniteCert.lean` from mathematical spec |

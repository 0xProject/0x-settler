# `ln` formal proof

Machine-checked Lean 4 proof that the compiled `lnWad` / `lnWadToRay` (from
`src/vendor/Ln.sol`, via `src/wrappers/LnWrapper.sol`) is correct against
`Real.log`. The proof runs against the EVMYulLean interpretation of the Yul that
`solc` emits — there is no second hand-maintained model of the implementation.

## Start here

* **`LnProof/Theorems.lean`** — the signpost. Every proven property of the
  compiled runtime, restated explicitly, plus the `#guard_msgs` axiom gate that
  pins each to `propext`, `Classical.choice`, `Quot.sound`.
* **`LnProof/Correct.lean`** — the public correctness proofs (Real.log bracket,
  monotonicity, reverts, sign, zero-at-`1`).
* **`LnProof/ErrorBoundRuntime.lean`** — the runtime `1.6986`-ulp error bound.

## The proof in four seams

```
 compiled Yul runtime   run_ln_wad_to_ray_evm          LnProof/LnYulRuntime.lean (generated)
        │  seam 1: runtime ↔ model                     Seam/RuntimeModel.lean
 hand model             lnWadToRayBody                  Model/Body.lean
        │  seam 2: model ⊨ floor/cut spec              Floor/Spec.lean, Floor/CutEquiv.lean
 floor-cut spec         FloorSpecA / FloorSpecB         Floor/Spec.lean
        │  seam 3: floor ↔ arithmetized cut            Floor/CutEquiv.lean
 real-free cut spec     CutLnWadRayBracket              Spec/Cut.lean
        │  seam 4: cut ↔ Real.log                      Seam/RealLog.lean
 public target          LnWadToRaySpec (Real.log)       Spec/Real.lean
```

## Layout (`LnProof/LnProof/`)

The directories are the proof's abstraction layers, lowest first; each has a
facade module (`Foundation.lean`, `Spec.lean`, …) re-exporting its public face.

| Directory      | Role |
|----------------|------|
| `Foundation/`  | Domain-agnostic primitives: EVM-word transport (`Word`, `WordDiv`), `ExpSum` (Taylor partial sums), polynomial/Kronecker cert machinery (`Poly`, `ShiftCert`, `Kronecker`, `KroneckerShift`). |
| `Spec/`        | What "correct" means: `Real` (the `Real.log` target) and `Cut` (its real-free arithmetization). |
| `Model/`       | `Body` — the reference implementation (`lnWadToRayBody` / `lnWadBody`). |
| `Mono/`        | Monotonicity of the model over its domain (`Top` is the entry point). |
| `Floor/`       | The model ⊨ floor/cut spec proof and its bracket/cap/cert machinery. |
| `Error/`       | The model-level `1.6986`-ulp error bound and its cell covers / caps. |
| `Seam/`        | The semantic bridges: `RuntimeModel` (runtime ↔ model) and `RealLog` (cut ↔ `Real.log`). |
| `Cert/`        | **Generated** certificate literals and cell covers — machine output, do not edit. |
| (top level)    | `Theorems`, `Correct`, `ErrorBoundRuntime`, and the two generated EVM artifacts `LnYulRuntime` / `LnYulProof`. |

## Build

```bash
cd formal/ln/LnProof && lake build
```

A green build runs the axiom gate in `Theorems.lean`.

## Regenerate

The two **generated EVM artifacts** (`LnYulRuntime.lean`, `LnYulProof.lean`,
ignored) come from the compiled Yul via the shared importer:

```bash
lake -d formal/yul build yul_importer
./formal/yul/generate_from_forge.sh ln \
  src/wrappers/LnWrapper.sol:LnWrapper \
  formal/ln/LnProof/LnProof/LnYul.lean 0.8.34
```

The **generated certificates** under `Cert/` (ignored) come from the in-tree
generators, run from `formal/ln/LnProof`:

```bash
lake build LnProof.Floor.CertDefs LnProof.Foundation.KroneckerShift LnProof.Floor.Consts
lake env lean GenFloorCertLit.lean
lake build LnProof.Cert.FloorCertLit
lake env lean GenCover.lean
lake env lean GenErr1.lean
lake build LnProof.Error.Core
lake env lean GenErrLit.lean
```

See `.github/workflows/ln-formal.yml` for the canonical CI sequence.

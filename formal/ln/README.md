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

The directories are the proof's abstraction layers, lowest first. The root
`LnProof.lean` is the checked aggregate of their public entry modules.

| Directory      | Role |
|----------------|------|
| `Foundation/`  | Domain-agnostic EVM-word transport (`Word`, `WordDiv`). The Taylor partial sums and the polynomial/Kronecker certificate machinery live in the shared `Common` package (`Common.Exp`, `Common.Poly`). |
| `Spec/`        | What "correct" means: `Real` (the `Real.log` target) and `Cut` (its real-free arithmetization). |
| `Model/`       | `Body` — the reference implementation (`lnWadToRayBody` / `lnWadBody`). |
| `Mono/`        | Monotonicity of the model over its domain (`Top` is the entry point). |
| `Floor/`       | The model ⊨ floor/cut spec proof and its bracket/cap/cert machinery. |
| `Error/`       | The model-level `1.6986`-ulp error bound and its cell covers / caps. |
| `Seam/`        | The semantic bridges: `RuntimeModel` (runtime ↔ model) and `RealLog` (cut ↔ `Real.log`). |
| `Cert/`        | **Generated** certificate literals, cells, and aggregate covers — machine output, do not edit. |
| (top level)    | `Theorems`, `Correct`, `ErrorBoundRuntime`, and the two generated EVM artifacts `LnYulRuntime` / `LnYulProof`. |

## Build

After the generated sources described below are present:

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
find LnProof/Cert -type f ! -name .gitkeep -delete
find LnProof/Cert -depth -type d -empty ! -path LnProof/Cert -delete
for path in .lake/build/lib/lean/LnProof/Cert .lake/build/ir/LnProof/Cert; do
  if [[ -e "$path" ]]; then
    rm -r -- "$path"
  fi
done
lake build LnProof.Floor.CertDefs Common.Foundation.KroneckerShift LnProof.Floor.Consts Common.GenCover
lake env lean GenFloorCertLit.lean
lake build \
  LnProof.Cert.FloorCertGeLoLit \
  LnProof.Cert.FloorCertLtLoLit
lake env lean GenCover.lean
lake env lean GenErr1.lean
lake build \
  LnProof.Floor.CarryIndependent.Approximation \
  Common.GenBernstein \
  Common.Foundation.PackedShift
lake env lean GenApproximationCert.lean
lake build LnProof.Error.Core.Budget
lake env lean GenErrLit.lean
lake build
```

`GenCover.lean` emits each floor certificate's cells and its complete generated
aggregate; the checked-in floor modules supply the polynomial-evaluation bridge.
`GenErrLit.lean` emits the complete specialized error-bound cover.
`GenApproximationCert.lean` emits two approximation-envelope covers containing
310 cells: 291 use a packed Kronecker shift followed by interval Horner, and 19
use Bernstein witnesses. Four contiguous dependency lanes connect the cells to
an aggregate that imports only their tips. A separate Bernstein certificate
bounds the ratio gap induced by the variable-propagated numerator and
denominator errors by its endpoint value.

See `.github/workflows/formal.yml` for the canonical CI sequence.

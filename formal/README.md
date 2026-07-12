# Formal Verification

The `formal` tree contains Lean 4 proofs for the fixed-point and wide-integer
math libraries used by Settler. Solidity is the implementation source of
truth. Runtime proofs consume Yul emitted from the Solidity build; they do not
maintain a second executable implementation in Lean.

## Verified interfaces

| Proof package | Solidity source | Verified surface |
|---|---|---|
| `sqrt/SqrtProof` | `src/vendor/Sqrt.sol` | `_sqrt`, `sqrt`, and `sqrtUp` on `uint256` |
| `sqrt/Sqrt512Proof` | `src/utils/512Math.sol` | 512-bit square root against `Nat.sqrt` |
| `cbrt/CbrtProof` | `src/vendor/Cbrt.sol` | `_cbrt`, `cbrt`, and `cbrtUp` on `uint256` |
| `cbrt/Cbrt512Proof` | `src/utils/512Math.sol` | 512-bit cube root against the integer cube-root specification |
| `ln/LnProof` | `src/vendor/Ln.sol` | `lnWadToRay` and `lnWad` against `Real.log`, including domains, error, and monotonicity |
| `exp/ExpProof` | `src/vendor/Exp.sol` | `expRayToWad` and `mulExpRay` against `Real.exp`, including domains, error brackets, monotonicity, and the central logarithm round trip |

## Package architecture

The transitive reduction of the shared and proof-specific package graph is:

```text
EVMYulLean ──> FormalYul ──> Common ──> LnProof ──> ExpProof
                    │
                    ├───────────────> SqrtProof ──> Sqrt512Proof
                    │
                    └───────────────> CbrtProof ──> Cbrt512Proof
```

`FormalYul` supplies the generated-Yul runtime model, interpreter bridges, and
preservation lemmas. `Common` contains proof infrastructure shared by the
transcendental packages, including exact polynomial evaluation and finite
interval certificate checkers. `ExpProof` imports `LnProof` because its public
surface includes a round-trip theorem.

Each runtime proof follows the same data flow:

1. Forge asks the pinned solc version for the wrapper contract's Yul IR.
2. The Yul importer emits `*YulRuntime.lean` and `*YulProof.lean` modules.
3. Arithmetic modules relate the emitted word-level program to integer and
   real-number specifications.
4. The package root imports the public theorems and checks their axiom sets.

Generated runtime modules and generated certificate modules are ignored by
Git. On a package-cache miss, CI clears their declared output surfaces,
regenerates them once, and builds the package. Exact package-cache hits skip
generation and the package build. Package caches contain the generated sources
beside their Lake outputs, so a dependent job receives the source corresponding
to each cached `.olean` file.

## Trust model

The public theorem surface is accepted by the Lean kernel under the standard
axioms `propext`, `Classical.choice`, and `Quot.sound`. Each package has an
axiom gate in `AxiomCheck.lean` or `Theorems.lean`; the build fails if a gated
theorem acquires another axiom.

The trusted path consists of:

- the Lean kernel and the definitions of the mathematical specifications;
- the EVM/Yul semantics used by EVMYulLean and the bridge from emitted Yul to
  those semantics;
- the pinned Solidity compiler and Forge used to obtain Yul IR from Solidity
  source;
- the GitHub Actions runner, action implementations, artifact and cache
  services, and Mathlib cache distribution used by CI.

Certificate generators, interval splitters, Python scripts, and coefficient
search programs are proof producers, not trusted proof checkers. Their output
contains literals, interval endpoints, or algebraic witnesses. Lean recomputes
the relevant polynomial identities, range conditions, and sign checks in the
kernel. A malformed certificate therefore fails to elaborate or fails its
theorem.

On a cache miss or non-exact prefix restore, CI removes each declared generated
file and the contents of each declared generated-only directory. It runs the
generator once, requires every declared output to be nonempty, requires tracked
sources to remain unchanged, and then builds the package. A malformed
certificate fails when Lean consumes it.

Exact package-cache hits are trusted proof artifacts: CI does not rerun their
generators or Lean package builds. Build caches and the cache service are
therefore part of the CI supply chain. Cache keys cover the package's semantic
inputs, while Lake hashes module sources, options, imports, and imported
outputs when producing a fresh artifact.

When its ignored source directories are absent, EVMYulLean's Lake build clones
the default branches of `sha-2` and `SHA3IUF`. Their resolved commits are not
part of the formal-tool cache key. A cold publisher therefore resolves those
branches, and subsequent jobs trust the formal-tool artifact it publishes.

## CI and cache boundaries

The unified formal workflow keeps the large Mathlib and Lake dependency outputs
in a cache keyed only by the pinned toolchain and dependency manifests. A
separate formal-tool cache contains `FormalYul` and EVMYulLean outputs and is
keyed by their sources as well as that dependency configuration. Every proof
package has a separate cache. A package's exact key includes:

- the source hash of each direct dependency;
- its Lake configuration and Lean sources;
- the Solidity, wrapper, and Forge inputs that determine its emitted Yul;
- the package-local composite action that contains its generator invocations,
  plus the shared setup, package-cache, generation, and dependency-cache
  actions involved in its build.

One base job owns the dependency and formal-tool cache keys. Each proof package
job is the sole publisher of its package key. A publisher may restore an older
prefix, regenerate on the resulting non-exact hit, and save the exact key after
a successful build. Downstream jobs start through `needs`, restore only the
exact key produced by their publisher, and fail if it is unavailable.

The checked-in path router selects affected packages and closes the package
dependencies before jobs start. Thus an Exp change schedules `Common`,
`LnProof`, and `ExpProof`; a 512-bit proof schedules its 256-bit dependency.
Unchanged exact package keys skip their package work. Changes to shared formal
tooling schedule every package.

The 512-bit generation keys include the exact forge-std `IERC20` interface
pulled into the compiled source closure through `Ternary.sol`.

The canonical job graph and pinned compiler versions are in
`.github/workflows/formal.yml` and the composite actions under
`.github/actions/`. Local runs should execute the same generation steps before
`lake build`.

## Current certificate domain

The shared finite-cover machinery proves nonnegativity of an integer
polynomial on a compact integer interval. Rational inequalities use it after
clearing a denominator whose sign has been proved separately. Transcendental
inequalities use rational Taylor bounds to reduce the remaining obligation to
polynomial signs. Piecewise proofs partition the compact domain and check each
cell independently.

### Certificate backend interface

Every polynomial-sign backend exports the same proposition:

```lean
def NonnegOn (cs : List Int) (lo hi : Int) : Prop :=
  ∀ x : Int, lo ≤ x → x ≤ hi → 0 ≤ evalPoly cs x
```

The interval-Horner/Kronecker backend shifts the polynomial to each cell's
left endpoint, packs the candidate shifted coefficients at radix `2^B`, and
checks coefficient bounds plus one exact evaluation identity. Interval Horner
then proves the packed shifted polynomial nonnegative throughout the cell.
`checkCoverK_nonnegOn` turns an accepted cell walk into `NonnegOn` for the
original polynomial.

The Bernstein backend represents the degree-scaled polynomial as a sum of
Bernstein basis polynomials. `checkBernsteinKWithWitness` checks that the
weights are nonnegative, both polynomial coefficient norms fit below the
chosen radix, and one exact evaluation identity establishes equality of the
two integer polynomials. `checkBernsteinKWithWitness_nonnegOn` turns an
accepted witness into the same `NonnegOn` proposition. Consumers therefore do
not depend on which checker produced a cell theorem.

A new backend integrates through four concrete pieces:

1. Define a Boolean checker whose inputs contain every untrusted witness.
2. Prove that a `true` checker result implies `NonnegOn` without adding an
   axiom or trusting the witness producer.
3. Provide a `CellEmitter` and a generator that emit the checker theorem and
   its `NonnegOn` consequence for each cell.
4. Add an executable example showing that at least one malformed witness is
   rejected. `Common.CertificateExamples` contains the corresponding
   Bernstein examples for missing weights, a reversed interval, and an
   insufficient identity width.

This machinery directly covers:

- univariate integer or rational-polynomial inequalities on closed intervals;
- finite piecewise envelopes with exact rational endpoints;
- transcendental bounds after an explicit polynomial remainder theorem;
- word-level algorithms after floors, divisions, and signed-word operations
  have been bridged to suitable integer inequalities.

It does not by itself retain correlations among several variables, quotient
remainders, modular residues, or successive floor errors. Those relations must
be preserved in the theorem statement or discharged by another certificate
system.

## Runtime-tree elaboration discipline

Runtime normal forms such as `evTree`, `r0MulTree`, and `mulShiftTree` are
shared DAGs represented by deeply nested `evm*` terms. Tactics that repeatedly
normalize those terms can traverse an exponentially larger syntax tree.

Arithmetic proofs name a tree-valued word before invoking such tactics:

```lean
set w := runtimeTree x with hw
clear_value w
```

Facts requiring the definition are established before `clear_value`; later
steps reason about the opaque local. Term-level order lemmas or tactics with an
explicit, small hypothesis set are used where general preprocessing would
unfold the runtime tree.

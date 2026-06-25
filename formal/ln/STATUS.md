# `formal/ln` proof status

This package reasons about the natural-log routine `Ln.lnWadToRay` / `Ln.lnWad`
(`src/vendor/Ln.sol`).

## Proven (verified by `lake build`; axiom-clean)

- **Math layer** (`LnRealBridge`, `ExpSum`, `LnRealSpec`): an arithmetized exponential/log
  cut is bridged to Mathlib's real `Real.log`. The fixed-point spec is
  `LnWadToRaySpec x r := (r : ℝ) ≤ 10²⁷·log(x/10¹⁸) < r + 2`. No homegrown logarithm — the
  target is the genuine real logarithm.
- **Model layer** (`Stages.lnWadToRayBody`, `FloorSpec`, `TopMono`/`LnMono`, `ErrorBound*`,
  and the generated, kernel-checked certificates): the model satisfies the cut bracket, is
  monotone over the whole domain (within-octave, all octave seams, and the `x = 10¹⁸`
  correction), is negative iff `x < 10¹⁸`, and is exactly `0` at `x = 10¹⁸`.
- **Compiled-runtime ↔ model equivalence** (`LnYulBody`): `run_ln_wad_to_ray_evm_eq_body`
  proves the compiled `LnWrapper` `lnWadToRay` runtime returns exactly
  `Stages.lnWadToRayBody (u256 x)` for positive inputs — by symbolic execution of the
  EVMYulLean interpreter over the `forge inspect` Yul (signed-opcode bridges `wordNat_sar`/
  `wordNat_sdiv`, the `slt`-guard decision, and the sharing-preserving close). This anchors
  the model to the exact compiled code: a wrong transcribed constant/shift would break it.
- **`lnWadToRay` runtime correctness — unconditional** (`LnYulCorrect.lnWadToRayRuntimeCorrect`):
  for every 256-bit input the compiled `lnWadToRay` runtime is correct against the `Real.log`
  spec, with **no `CutCorrect` hypothesis**. `AxiomCheck` pins it to
  `[propext, Classical.choice, Quot.sound]`.

## Remaining

- **Wad path**: `run_ln_wad_evm_eq_body` (the `lnWad` runtime equals `Stages.lnWadBody`) and
  the corresponding unconditional `lnWadRuntimeCorrect` discharge. `lnWadRuntimeCorrect_of_cutCorrect`
  is currently still conditional on `CutCorrect` for the wad path.
- **Revert**: `run_ln_wad_*_evm_revert` (the runtime reverts for `x ≤ 0`) and the
  `…RevertsNonpositive` discharge.
- **Runtime-level transports**: restating monotonicity, the sign property, and exact-0 at the
  runtime level (they are proven for the model and transfer via the equivalence).

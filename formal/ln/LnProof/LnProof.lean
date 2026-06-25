-- This module serves as the root of the `LnProof` library.
-- Import modules here that should be built as part of the library.
import LnProof.LnYulCorrect
import LnProof.LnYulBody
import LnProof.TopMono
import LnProof.FloorSpec
import LnProof.ExpLogCutSpec
import LnProof.ErrorBound
import LnProof.AxiomCheck

/-!
# LnProof

Status summary — see `formal/ln/STATUS.md` for detail.

`LnYulCorrect.lnWadToRayRuntimeCorrect` is **unconditional and axiom-clean**: the compiled
`LnWrapper` `lnWadToRay` runtime is proven correct against Mathlib's `Real.log` fixed-point
spec for every 256-bit input, with no `CutCorrect` hypothesis. The bridge is
`LnYulBody.run_ln_wad_to_ray_evm_eq_body` (the compiled body equals `Stages.lnWadToRayBody`),
composed with the cut→`Real.log` bridge. The wad path
(`LnYulCorrect.lnWadRuntimeCorrect_of_cutCorrect`) is still conditional on `CutCorrect`, and
the `…RevertsNonpositive` / runtime-level monotonicity/sign/exact-0 facts are not yet wired.
-/

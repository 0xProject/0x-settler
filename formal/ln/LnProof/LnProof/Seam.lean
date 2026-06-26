/-!
# Seam facade

The two semantic bridges. `RuntimeModel` proves the compiled runtime
(`run_ln_wad_*_evm`) equals the hand model (`Model.Body`); `RealLog` bridges
the real-free cut predicates to `Real.log`. Together they connect the
implementation to the `Real.log` specification.
-/
import LnProof.Seam.RuntimeModel
import LnProof.Seam.RealLog

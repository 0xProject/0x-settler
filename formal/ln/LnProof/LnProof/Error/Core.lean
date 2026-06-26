import LnProof.Floor.CutEquiv
import LnProof.Error.Cert
import LnProof.Error.Core.CutDefs
import LnProof.Error.Core.ExpMargin
import LnProof.Error.Core.Args
import LnProof.Error.Core.Residue
import LnProof.Error.Core.ResidueCover
import LnProof.Error.Core.Budget
import LnProof.Error.Core.PhaseGe
import LnProof.Error.Core.Direct
import LnProof.Error.Core.PhaseCover
import LnProof.Error.Core.PhaseLt
import LnProof.Error.Core.Bounds
import LnProof.Error.Core.C160
import LnProof.Error.Core.BranchPos
import LnProof.Error.Core.BranchNeg
import LnProof.Error.Core.BranchBn
import LnProof.Error.Core.Assembly
import LnProof.Error.Core.BranchCert

/-!
# Public cut statement for the `lnWadToRay` error bound

This module re-exports the error-bound machinery, decomposed into the
`Error/Core/` components (see each for its role). The upper side is a
rational strict upper cut over denominator `QS * den`; the lower side is
the established floor cut.
-/

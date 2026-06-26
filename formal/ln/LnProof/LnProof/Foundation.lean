/-!
# Foundation facade

Domain-agnostic primitives shared across the proof: EVM-word arithmetic
transport (`Word`, `WordDiv`), the exponential partial-sum interface
(`ExpSum`), and the polynomial-positivity / Kronecker certificate machinery
(`Poly`, `ShiftCert`, `Kronecker`, `KroneckerShift`). No `lnWad`-specific
semantics live here.
-/
import LnProof.Foundation.Word
import LnProof.Foundation.WordDiv
import LnProof.Foundation.ExpSum
import LnProof.Foundation.Poly
import LnProof.Foundation.ShiftCert
import LnProof.Foundation.Kronecker
import LnProof.Foundation.KroneckerShift

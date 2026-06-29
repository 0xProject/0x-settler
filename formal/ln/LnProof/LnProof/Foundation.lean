/-!
# Foundation facade

Domain-agnostic primitives this proof relies on: EVM-word arithmetic transport
(`Word`, `WordDiv`, local), plus the function-agnostic machinery from the
shared `Common` package — the exponential partial-sum interface (`Common.Exp`)
and the polynomial-positivity / Kronecker certificate machinery
(`Common.Poly`). No `lnWad`-specific semantics live here.
-/
import LnProof.Foundation.Word
import LnProof.Foundation.WordDiv
import Common.Foundation.ExpSum
import Common.Foundation.Poly
import Common.Foundation.ShiftCert
import Common.Foundation.Kronecker
import Common.Foundation.KroneckerShift

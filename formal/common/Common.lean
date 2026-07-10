-- This module serves as the root of the `Common` library: the shared,
-- function-agnostic Lean machinery used by the per-function Yul correctness
-- proofs (`LnProof`, `ExpProof`). Nothing here models any specific
-- implementation. It is generic interval-Horner and Bernstein nonnegativity
-- certificates and Kronecker identity-testing / packed-shift cell walks
-- (`Common.Poly`), the
-- `e^(p/q)` Taylor-cut framework (`Common.Exp`), the `Real.exp` bridge for the
-- partial-sum caps (`Common.RealExpBridge`), the EVM-word op-preservation
-- bridges (`Common.Word`), and the certificate generator string/IO helpers the
-- `lake env lean Gen*.lean` scripts share.
import Common.Word
import Common.Foundation.Poly
import Common.Foundation.ExpSum
import Common.Foundation.ShiftCert
import Common.Foundation.Kronecker
import Common.Foundation.KroneckerShift
import Common.Foundation.Bernstein
import Common.Seam.RealExpBridge
import Common.GenCover
import Common.GenBernstein
import Common.CertificateExamples

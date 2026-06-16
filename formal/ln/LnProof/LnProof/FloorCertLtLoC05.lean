import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell05 : checkCoverK kB certLtLoLit 40683318943956774759765093062 40933137699355212682659008289
    [249818755398437922893915227] = true := by
  decide +kernel

end LnFloorCert

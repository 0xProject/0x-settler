import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell05 : checkCoverK kB certLtLoLit 40683318943956774759765093062 40933137699355212682659008289
    [247335437333490015576583371, 2483318064947907317331855] = true := by
  decide +kernel

end LnFloorCert

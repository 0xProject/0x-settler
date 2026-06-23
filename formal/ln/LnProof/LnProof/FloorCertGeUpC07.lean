import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell07 : checkCoverK kB certGeUpLit 72408786498893991617815899219 75861708703758292357820627133
    [3451099309101645344988055496, 1822895762655395016672417] = true := by
  decide +kernel

end LnFloorCert

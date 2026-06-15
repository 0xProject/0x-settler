import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell07 : checkCoverK kB certGeUpLit 72408786498893991617815899219 75861708703758292357820627133
    [3452922204864300740004727914] = true := by
  decide +kernel

end LnFloorCert

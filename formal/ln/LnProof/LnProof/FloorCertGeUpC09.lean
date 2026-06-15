import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell09 : checkCoverK kB certGeUpLit 76378456004808706114825201879 76545585265581278814137973750
    [167129260772572699312771871] = true := by
  decide +kernel

end LnFloorCert

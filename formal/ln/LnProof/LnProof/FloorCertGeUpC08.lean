import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell08 : checkCoverK kB certGeUpLit 75861708703758292357820627134 76378401319591968748569314938
    [510085744815753249492106812, 6606871017923141256580991] = true := by
  decide +kernel

end LnFloorCert

import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell08 : checkCoverK kB certGeUpLit 75861708703758292357820627134 76378401319591968748569314938
    [516692615833676390748687804] = true := by
  decide +kernel

end LnFloorCert

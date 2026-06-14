import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell03 : checkCoverK kB certGeUpLit 17058948831182728858990682241133 18269742959824067297062437976749
    [1210794128641338438071755735616] = true := by
  decide +kernel

end LnFloorCert

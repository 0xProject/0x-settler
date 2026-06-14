import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell02 : checkCoverK kB certGeUpLit 16773635833163794244906404107707 17058948831182728858990682241132
    [285312998018934614084278133425] = true := by
  decide +kernel

end LnFloorCert

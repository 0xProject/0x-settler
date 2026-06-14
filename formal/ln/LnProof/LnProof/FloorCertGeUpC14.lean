import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell14 : checkCoverK kB certGeUpLit 20217130875292592156275203260041 20282409603651670423947251286015
    [65278728359078267672048025974] = true := by
  decide +kernel

end LnFloorCert

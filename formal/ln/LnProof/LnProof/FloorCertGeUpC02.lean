import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell02 : checkCoverK kB certGeUpLit 60868942551995640788375953629 65647205322201657485063864879
    [4778262770206016696687911250] = true := by
  decide +kernel

end LnFloorCert

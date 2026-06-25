import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell04 : checkCoverK kB certGeUpLit 66268224935948723932208112263 71273341474262273478494121528
    [5005116538313549546286009265] = true := by
  decide +kernel

end LnFloorCert

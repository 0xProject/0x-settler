import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell13 : checkCoverK kB certGeUpLit 20216488897356280165336263304740 20282409603651670423947251286015
    [65920706295390258610987981275] = true := by
  decide +kernel

end LnFloorCert

import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell08 : checkCoverK kB certGeUpLit 75848344205939394473959398559 76368615273267926498199066888
    [520271067328532024239668329] = true := by
  decide +kernel

end LnFloorCert

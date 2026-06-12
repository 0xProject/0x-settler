import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell05 : checkCoverK 38000 certLtUpLit 10708806721825835211973625643013 10844855617825835211973625643013
    [136048896000000000000000000000] = true := by
  decide +kernel

end LnFloorCert

import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell06 : checkCoverK kB certLtUpLit 10844855617825835211973625643014 11334631643425835211973625643014
    [489776025600000000000000000000] = true := by
  decide +kernel

end LnFloorCert

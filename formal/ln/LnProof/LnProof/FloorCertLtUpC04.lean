import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell04 : checkCoverK 38000 certLtUpLit 10633224001825835211973625643012 10708806721825835211973625643012
    [75582720000000000000000000000] = true := by
  decide +kernel

end LnFloorCert

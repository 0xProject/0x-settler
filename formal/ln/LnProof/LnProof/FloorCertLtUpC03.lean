import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell03 : checkCoverK kB certLtUpLit 10297300801825835211973625643011 10633224001825835211973625643011
    [335923200000000000000000000000] = true := by
  decide +kernel

end LnFloorCert

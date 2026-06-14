import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell07 : checkCoverK kB certLtUpLit 11334631643425835211973625643015 11555030854945835211973625643015
    [220399211520000000000000000000] = true := by
  decide +kernel

end LnFloorCert

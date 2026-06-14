import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell00 : checkCoverK kB certLtUpLit 10141204801825835211973625643008 10235556958232307525494886028008
    [94352156406472313521260385000] = true := by
  decide +kernel

end LnFloorCert

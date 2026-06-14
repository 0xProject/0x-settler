import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell03 : checkCoverK kB certLtUpLit 10305530652815519157653642498120 10675447966833128826886697468907
    [369917314017609669233054970787] = true := by
  decide +kernel

end LnFloorCert

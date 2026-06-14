import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell08 : checkCoverK kB certLtUpLit 10779963205013996747845870058713 10828761738119364680208728770969
    [48798533105367932362858712256] = true := by
  decide +kernel

end LnFloorCert

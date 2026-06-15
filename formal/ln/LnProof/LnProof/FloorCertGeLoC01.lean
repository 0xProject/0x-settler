import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell01 : checkCoverK kB certGeLoLit 62248862404922033823954520839 63042223622777199713651466026
    [793361217855165889696945187] = true := by
  decide +kernel

end LnFloorCert

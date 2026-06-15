import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell10 : checkCoverK kB certGeLoLit 77437455442871642444333051411 77857297359333941978235389794
    [419841916462299533902338383] = true := by
  decide +kernel

end LnFloorCert

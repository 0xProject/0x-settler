import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell04 : checkCoverK kB certLtUpLit 40224348129155411324248597879 40237671635020882839496520159
    [13323505865471515247922280] = true := by
  decide +kernel

end LnFloorCert

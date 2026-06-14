import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell01 : checkCoverK kB certLtUpLit 10235556958232307525494886028009 10278716364765519398518749303920
    [43159406533211873023863275911] = true := by
  decide +kernel

end LnFloorCert

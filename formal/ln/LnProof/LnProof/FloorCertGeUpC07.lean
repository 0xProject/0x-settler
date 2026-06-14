import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell07 : checkCoverK kB certGeUpLit 19575368566221044162595721694280 20121813700701489583336428308765
    [546445134480445420740706614485] = true := by
  decide +kernel

end LnFloorCert

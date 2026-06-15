import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell09 : checkCoverK kB certLtUpLit 42243140642141618723122083989 44761456068401282094658552447
    [2518315426259663371536468458] = true := by
  decide +kernel

end LnFloorCert

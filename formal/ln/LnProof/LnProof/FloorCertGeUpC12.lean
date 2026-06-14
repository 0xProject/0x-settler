import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell12 : checkCoverK kB certGeUpLit 20182572396030540906326124652210 20198185050312597011198675301886
    [15612654282056104872550649676] = true := by
  decide +kernel

end LnFloorCert

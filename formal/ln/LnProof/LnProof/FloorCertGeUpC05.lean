import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell05 : checkCoverK kB certGeUpLit 71285905378028973084942956447 71968434253869915164444390522
    [682528875840942079501434075] = true := by
  decide +kernel

end LnFloorCert

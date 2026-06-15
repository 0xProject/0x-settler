import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell11 : checkCoverK kB certGeUpLit 78599479677287894832822182126 78838288976975033931214462307
    [238809299687139098392280181] = true := by
  decide +kernel

end LnFloorCert

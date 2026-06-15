import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell10 : checkCoverK kB certGeUpLit 76545585265581278814137973751 78599479677287894832822182125
    [2053894411706616018684208374] = true := by
  decide +kernel

end LnFloorCert

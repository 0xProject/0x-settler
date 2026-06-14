import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell08 : checkCoverK kB certLtUpLit 11611358934728331263016579609047 12580407414500243265481207840047
    [969048479771912002464628231000] = true := by
  decide +kernel

end LnFloorCert

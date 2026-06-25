import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell05 : checkCoverK kB certLtUpLit 40237671635020882839496520160 40258748239835768207775715658
    [21076604814885368279195498] = true := by
  decide +kernel

end LnFloorCert

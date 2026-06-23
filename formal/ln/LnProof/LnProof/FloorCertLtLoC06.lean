import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell06 : checkCoverK kB certLtLoLit 40933137699355212682659008290 41019543030322903743594235649
    [79665791422051657107266464, 6739539545639403827960894] = true := by
  decide +kernel

end LnFloorCert

import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell05 : checkCoverK kB certGeLoLit 69233132140651152842861403917 69643680272268497720544738509
    [410548131617344877683334592] = true := by
  decide +kernel

end LnFloorCert

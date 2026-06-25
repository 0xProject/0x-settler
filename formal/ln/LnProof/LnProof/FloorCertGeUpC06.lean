import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell06 : checkCoverK kB certGeUpLit 71949306592399438020188468465 72253963783645493179901998777
    [304657191246055159713530312] = true := by
  decide +kernel

end LnFloorCert

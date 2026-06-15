import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell04 : checkCoverK kB certGeLoLit 68717226458158102762251661878 69233034096605084266152150503
    [515807638446981503900488625] = true := by
  decide +kernel

end LnFloorCert

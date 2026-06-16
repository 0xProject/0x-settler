import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell04 : checkCoverK kB certGeLoLit 68717504609657537844941640471 69233132140651152842861403916
    [515627530993614997919763445] = true := by
  decide +kernel

end LnFloorCert

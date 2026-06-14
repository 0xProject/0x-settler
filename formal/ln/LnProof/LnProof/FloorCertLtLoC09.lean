import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell09 : checkCoverK kB certLtLoLit 11885210362657835211973625643017 12242257085320235211973625643017
    [357046722662400000000000000000] = true := by
  decide +kernel

end LnFloorCert

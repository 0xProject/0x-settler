import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell12 : checkCoverK kB certLtLoLit 47296264120598942405857135302 51908282562281673025522611127
    [4607495457591173783301026048, 4522984091556836364449776] = true := by
  decide +kernel

end LnFloorCert

import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell04 : checkCoverK kB certLtLoLit 39782184972069981508068781992 40683318943956774759765093061
    [900422074251608552305128931, 711897635184699391182137] = true := by
  decide +kernel

end LnFloorCert

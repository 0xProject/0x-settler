import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell06 : checkCoverK kB certLtUpLit 41692588105644715585450931158 42015714968624513035526540308
    [323126862979797450075609150] = true := by
  decide +kernel

end LnFloorCert

import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell15 : checkCoverK kB certErrLtLit 43441958359528469510743996389 43550321627651620471295348779
    [108363268123150960551352390] = true := by
  decide +kernel

end LnFloorCert

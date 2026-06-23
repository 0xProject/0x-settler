import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell04 : checkCoverK kB certGeUpLit 66326012476199512076492819331 71285905378028973084942956446
    [4956925658766648405965496596, 2967243062812602484640518] = true := by
  decide +kernel

end LnFloorCert

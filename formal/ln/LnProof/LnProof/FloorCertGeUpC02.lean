import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell02 : checkCoverK kB certGeUpLit 15582362972005525091920552059200 16805676617545692639475832291230
    [1223313645540167547555280232030] = true := by
  decide +kernel

end LnFloorCert

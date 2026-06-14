import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell01 : checkCoverK kB certGeUpLit 15175514278996281049189740636297 15582362972005525091920552059199
    [406848693009244042730811422902] = true := by
  decide +kernel

end LnFloorCert

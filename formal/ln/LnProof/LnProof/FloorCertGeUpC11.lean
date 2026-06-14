import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell11 : checkCoverK kB certGeUpLit 20064489913418975354158861265271 20162553774023688135563636774605
    [98063860604712781404775509334] = true := by
  decide +kernel

end LnFloorCert

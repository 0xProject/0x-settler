import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell09 : checkCoverK 38000 certGeLoLit 19348510451401251819195376186284 19705557174063651819195376186284
    [357046722662400000000000000000] = true := by
  decide +kernel

end LnFloorCert

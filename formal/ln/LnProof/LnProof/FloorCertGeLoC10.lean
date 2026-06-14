import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell10 : checkCoverK kB certGeLoLit 19705557174063651819195376186285 19835348970720956005264548083723
    [129791796657304186069171897438] = true := by
  decide +kernel

end LnFloorCert

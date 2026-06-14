import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell06 : checkCoverK kB certLtLoLit 10558260669641940953813244498372 11045875788223987512547846876913
    [487615118582046558734602378541] = true := by
  decide +kernel

end LnFloorCert

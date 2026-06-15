import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell05 : checkCoverK kB certLtLoLit 40683335622502973975961309910 40933163684002996933851849391
    [249828061500022957890539481] = true := by
  decide +kernel

end LnFloorCert

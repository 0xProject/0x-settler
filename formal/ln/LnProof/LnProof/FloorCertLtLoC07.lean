import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell07 : checkCoverK kB certLtLoLit 41019616312100785763631764707 42508799051393563554355157298
    [1489182739292777790723392591] = true := by
  decide +kernel

end LnFloorCert

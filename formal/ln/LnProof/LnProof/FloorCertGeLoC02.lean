import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell02 : checkCoverK kB certGeLoLit 16139278752360617268812773783960 16697056551612731524305339424315
    [557777799252114255492565640355] = true := by
  decide +kernel

end LnFloorCert

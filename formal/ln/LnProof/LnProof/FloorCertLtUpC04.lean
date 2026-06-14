import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell04 : checkCoverK kB certLtUpLit 10300290733559920510761662675179 10318581351720418835446063066151
    [18290618160498324684400390972] = true := by
  decide +kernel

end LnFloorCert

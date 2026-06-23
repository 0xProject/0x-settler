import LnProof.ErrCertGeLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errGe_cell05 : checkCoverK kB certErrGeLit 69150385520028080205898383828 69318984104385194428820826876
    [168598584357114222922443048] = true := by
  decide +kernel

end LnFloorCert

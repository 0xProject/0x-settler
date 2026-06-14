import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell02 : checkCoverK kB certLtUpLit 10283083180369672200219960462812 10305530652815519157653642498119
    [22447472445846957433682035307] = true := by
  decide +kernel

end LnFloorCert

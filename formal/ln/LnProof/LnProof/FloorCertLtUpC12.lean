import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell12 : checkCoverK kB certLtUpLit 45358461709730537512255462321 49100624827436726252807356861
    [3742163117706188740551894540] = true := by
  decide +kernel

end LnFloorCert

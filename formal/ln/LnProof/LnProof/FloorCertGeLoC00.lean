import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell00 : checkCoverK kB certGeLoLit 56022770974786139918731938273 62248862404922033823954520838
    [6226091430135893905222582565] = true := by
  decide +kernel

end LnFloorCert

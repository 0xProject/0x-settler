import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell00 : checkCoverK kB certGeLoLit 56022770974786139918731938273 62248863508307989581262617183
    [6221981203778697422681772771, 4111329743152239848906138] = true := by
  decide +kernel

end LnFloorCert

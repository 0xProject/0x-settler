import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell05 : checkCoverK kB certGeUpLit 71285921383811406182045145579 71968494449566398338160691002
    [682573065754992156115545423] = true := by
  decide +kernel

end LnFloorCert

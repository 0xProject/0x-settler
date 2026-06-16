import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell09 : checkCoverK kB certGeUpLit 76378401319591968748569314939 76545349455617885268024766253
    [166948136025916519455451314] = true := by
  decide +kernel

end LnFloorCert

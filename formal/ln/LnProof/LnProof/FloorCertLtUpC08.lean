import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell08 : checkCoverK kB certLtUpLit 42105474339119878441107071644 42243140642141618723122083988
    [137666303021740282015012344] = true := by
  decide +kernel

end LnFloorCert

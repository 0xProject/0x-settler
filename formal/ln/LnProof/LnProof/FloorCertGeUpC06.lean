import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell06 : checkCoverK kB certGeUpLit 71968434253869915164444390523 72408786498893991617815899218
    [352047579711659212169254941, 88304665312417241202253753] = true := by
  decide +kernel

end LnFloorCert

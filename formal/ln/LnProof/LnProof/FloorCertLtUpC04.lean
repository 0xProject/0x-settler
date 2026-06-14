import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell04 : checkCoverK kB certLtUpLit 10675447966833128826886697468908 10770151616997275407327261993131
    [94703650164146580440564524223] = true := by
  decide +kernel

end LnFloorCert

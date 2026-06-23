import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell14 : checkCoverK kB certLtUpLit 49670427525155949284453311470 56022770974786139918731938181
    [2109629451631523085440016752, 4242713997998667548838609958] = true := by
  decide +kernel

end LnFloorCert

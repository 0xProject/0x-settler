import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell14 : checkCoverK kB certLtLoLit 52718525787343046817539678214 56022770974786139918731938181
    [3304245187443093101192259967] = true := by
  decide +kernel

end LnFloorCert

import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell14 : checkCoverK kB certLtUpLit 49670405993033439910727072904 56022770974786139918731938181
    [6352364981752700008004865277] = true := by
  decide +kernel

end LnFloorCert

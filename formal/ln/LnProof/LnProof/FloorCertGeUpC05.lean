import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell05 : checkCoverK kB certGeUpLit 18249175332038711667734251217547 18423857642692923866673020234056
    [174682310654212198938769016509] = true := by
  decide +kernel

end LnFloorCert

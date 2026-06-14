import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell05 : checkCoverK kB certLtLoLit 10488077265272720113023495514353 10558260669641940953813244498371
    [70183404369220840789748984018] = true := by
  decide +kernel

end LnFloorCert

import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell04 : checkCoverK kB certGeUpLit 16979427757686177564090726988485 18249175332038711667734251217546
    [1269747574352534103643524229061] = true := by
  decide +kernel

end LnFloorCert

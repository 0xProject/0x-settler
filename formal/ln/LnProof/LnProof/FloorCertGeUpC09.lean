import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell09 : checkCoverK kB certGeUpLit 20188042491430430752648953056115 20217582813988731407505919116501
    [29540322558300654856966060386] = true := by
  decide +kernel

end LnFloorCert

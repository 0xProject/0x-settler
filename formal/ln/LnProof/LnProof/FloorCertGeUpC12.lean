import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell12 : checkCoverK kB certGeUpLit 78838288976975033931214462308 78899412729359578693986807700
    [61123752384544762772345392] = true := by
  decide +kernel

end LnFloorCert

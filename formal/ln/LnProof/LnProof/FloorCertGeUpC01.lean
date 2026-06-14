import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell01 : checkCoverK kB certGeUpLit 15212167328226586335452577096834 16773635833163794244906404107706
    [1561468504937207909453827010872] = true := by
  decide +kernel

end LnFloorCert

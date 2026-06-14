import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell10 : checkCoverK kB certGeUpLit 19682606610102545772726802791419 20064489913418975354158861265270
    [381883303316429581432058473851] = true := by
  decide +kernel

end LnFloorCert

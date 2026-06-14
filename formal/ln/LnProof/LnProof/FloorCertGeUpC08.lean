import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell08 : checkCoverK kB certGeUpLit 19234718785225251819195376186283 19470449219371196005264548083722
    [235730434145944186069171897439] = true := by
  decide +kernel

end LnFloorCert

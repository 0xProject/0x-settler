import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell08 : checkCoverK kB certGeUpLit 20121813700701489583336428308766 20188042491430430752648953056114
    [66228790728941169312524747348] = true := by
  decide +kernel

end LnFloorCert

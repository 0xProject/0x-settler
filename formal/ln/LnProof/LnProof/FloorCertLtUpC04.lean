import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell04 : checkCoverK kB certLtUpLit 40233044689780073357909666321 40276316995481393586173805059
    [43272305701320228264138738] = true := by
  decide +kernel

end LnFloorCert

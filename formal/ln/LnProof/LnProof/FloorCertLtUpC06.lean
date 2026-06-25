import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell06 : checkCoverK kB certLtUpLit 40258748239835768207775715659 41686814657515192596739173673
    [1428066417679424388963458014] = true := by
  decide +kernel

end LnFloorCert

import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell06 : checkCoverK kB certGeLoLit 19067888394773041807616703749813 19827011133089491901331066646783
    [759122738316450093714362896970] = true := by
  decide +kernel

end LnFloorCert

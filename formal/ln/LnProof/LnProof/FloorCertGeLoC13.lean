import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell13 : checkCoverK kB certGeLoLit 78000774274960452401547714171 79228162514264337593543950335
    [1227388239303885191996236164] = true := by
  decide +kernel

end LnFloorCert

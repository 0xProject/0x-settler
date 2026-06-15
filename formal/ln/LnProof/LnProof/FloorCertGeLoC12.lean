import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell12 : checkCoverK kB certGeLoLit 77947573405191424248689952844 78000774274960452401547714170
    [53200869769028152857761326] = true := by
  decide +kernel

end LnFloorCert

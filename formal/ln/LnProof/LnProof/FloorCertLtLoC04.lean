import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell04 : checkCoverK kB certLtLoLit 10184160994906416673806253181242 10414913185454529924459501364970
    [230752190548113250653248183728] = true := by
  decide +kernel

end LnFloorCert

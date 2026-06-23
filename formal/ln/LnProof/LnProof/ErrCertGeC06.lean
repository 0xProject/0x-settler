import LnProof.ErrCertGeLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errGe_cell06 : checkCoverK kB certErrGeLit 69318984104385194428820826877 73722346224426468943313592760
    [4403362120041274514492765883] = true := by
  decide +kernel

end LnFloorCert

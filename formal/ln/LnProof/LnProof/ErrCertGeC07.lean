import LnProof.ErrCertGeLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errGe_cell07 : checkCoverK kB certErrGeLit 73722346224426468943313592761 74321545568138162293005832386
    [599199343711693349692239625] = true := by
  decide +kernel

end LnFloorCert

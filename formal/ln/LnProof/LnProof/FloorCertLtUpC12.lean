import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell12 : checkCoverK kB certLtUpLit 45171106034455008017766705001 45304867147592323391712272578
    [133761113137315373945567577] = true := by
  decide +kernel

end LnFloorCert

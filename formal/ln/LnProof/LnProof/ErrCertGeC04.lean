import LnProof.ErrCertGeLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errGe_cell04 : checkCoverK kB certErrGeLit 68486183181351891943137631148 69150385520028080205898383827
    [664202338676188262760752679] = true := by
  decide +kernel

end LnFloorCert

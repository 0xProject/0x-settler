import LnProof.ErrCertGeLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errGe_cell03 : checkCoverK kB certErrGeLit 63240749540139122990169033121 68486183181351891943137631147
    [5245433641212768952968598026] = true := by
  decide +kernel

end LnFloorCert

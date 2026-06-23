import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell02 : checkCoverK kB certLtUpLit 40150853919271982033591711250 40205001758610997159114444920
    [51574324600738420243009639, 2573514738276705279724030] = true := by
  decide +kernel

end LnFloorCert

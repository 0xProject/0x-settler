import LnProof.ErrCertGeLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errGe_cell00 : checkCoverK kB certErrGeLit 56022770974786139918731938273 62235000306952571703781716893
    [6212229332166431785049778620] = true := by
  decide +kernel

end LnFloorCert

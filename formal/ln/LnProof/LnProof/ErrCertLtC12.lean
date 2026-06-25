import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell12 : checkCoverK kB certErrLtLit 43575643795639300685954607737 46777373364869912303362302353
    [3201729569230611617407694616] = true := by
  decide +kernel

end LnFloorCert

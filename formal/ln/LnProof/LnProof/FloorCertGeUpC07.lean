import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell07 : checkCoverK kB certGeUpLit 72253963783645493179901998778 75848344205939394473959398558
    [3594380422293901294057399780] = true := by
  decide +kernel

end LnFloorCert

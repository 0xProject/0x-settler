import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell07 : checkCoverK kB certLtUpLit 11484527015770799509484495012554 11611358934728331263016579609046
    [126831918957531753532084596492] = true := by
  decide +kernel

end LnFloorCert

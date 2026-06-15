import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell09 : checkCoverK kB certGeLoLit 74496930791525907093206183841 77437455442871642444333051410
    [2940524651345735351126867569] = true := by
  decide +kernel

end LnFloorCert

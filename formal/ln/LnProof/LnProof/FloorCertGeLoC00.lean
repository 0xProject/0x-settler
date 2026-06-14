import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell00 : checkCoverK kB certGeLoLit 14341829369545251819195376186275 15935787128948216066632449236205
    [1593957759402964247437073049930] = true := by
  decide +kernel

end LnFloorCert

import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell01 : checkCoverK kB certGeLoLit 15935787128948216066632449236206 16139278752360617268812773783959
    [203491623412401202180324547753] = true := by
  decide +kernel

end LnFloorCert

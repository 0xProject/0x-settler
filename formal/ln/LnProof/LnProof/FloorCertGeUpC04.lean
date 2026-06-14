import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell04 : checkCoverK kB certGeUpLit 18269742959824067297062437976750 18486789396570097711302005717406
    [217046436746030414239567740656] = true := by
  decide +kernel

end LnFloorCert

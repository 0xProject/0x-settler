import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell13 : checkCoverK kB certLtUpLit 49100624827436726252807356862 49670427525155949284453311469
    [551739808123961468120386483, 18062889595261563525568123] = true := by
  decide +kernel

end LnFloorCert

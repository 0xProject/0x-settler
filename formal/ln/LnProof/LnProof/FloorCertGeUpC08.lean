import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell08 : checkCoverK kB certGeUpLit 75861812401389825744148636454 76378456004808706114825201878
    [516643603418880370676565424] = true := by
  decide +kernel

end LnFloorCert

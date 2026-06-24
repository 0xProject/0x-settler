import LnProof.ErrCertLtC00
import LnProof.ErrCertLtC01
import LnProof.ErrCertLtC02
import LnProof.ErrCertLtC03
import LnProof.ErrCertLtC04
import LnProof.ErrCertLtC05
import LnProof.ErrCertLtC06
import LnProof.ErrCertLtC07
import LnProof.ErrCertLtC08
import LnProof.ErrCertLtC09
import LnProof.ErrCertLtC10
import LnProof.ErrCertLtC11
import LnProof.ErrCertLtC12
import LnProof.ErrCertLtC13
import LnProof.ErrCertLtC14
import LnProof.ErrCertLtC15

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

/-- The lt-branch error cell cover: `M'(m) ≥ 0` for all `m ∈ [2^95, Sc-46]`,
composed from the 16 `checkCoverK` cells. -/
theorem errLt_nonneg {m : Int}
    (h1 : 39614081257132168796771975168 ≤ m)
    (h2 : m ≤ 56022770974786139918731938181) :
    0 ≤ evalPoly certErrLtLit m := by
  rcases Int.lt_or_le m (39691126742571296271047700502 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell00 m (by omega) (by omega)
  rcases Int.lt_or_le m (39731844495833091299568641514 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell01 m (by omega) (by omega)
  rcases Int.lt_or_le m (39754544997383943847916639872 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell02 m (by omega) (by omega)
  rcases Int.lt_or_le m (39771161441046609927456741695 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell03 m (by omega) (by omega)
  rcases Int.lt_or_le m (40680904853992493020014255642 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell04 m (by omega) (by omega)
  rcases Int.lt_or_le m (40928811641811556050178946649 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell05 m (by omega) (by omega)
  rcases Int.lt_or_le m (41007581422239460128760466626 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell06 m (by omega) (by omega)
  rcases Int.lt_or_le m (41135431140835574713035759925 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell07 m (by omega) (by omega)
  rcases Int.lt_or_le m (43095658317834209710916769050 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell08 m (by omega) (by omega)
  rcases Int.lt_or_le m (43461765492999010618411064512 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell09 m (by omega) (by omega)
  rcases Int.lt_or_le m (43645705213556298311291468356 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell10 m (by omega) (by omega)
  rcases Int.lt_or_le m (46790509509991214314127230409 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell11 m (by omega) (by omega)
  rcases Int.lt_or_le m (47304945315436282108986587294 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell12 m (by omega) (by omega)
  rcases Int.lt_or_le m (51917938338423636963586449826 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell13 m (by omega) (by omega)
  rcases Int.lt_or_le m (52819343388154448027094034823 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell14 m (by omega) (by omega)
  exact checkCoverK_sound _ _ _ _ _ errLt_cell15 m (by omega) h2

end LnFloorCert

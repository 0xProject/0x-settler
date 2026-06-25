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
import LnProof.ErrCertLtC16
import LnProof.ErrCertLtC17

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

/-- The lt-branch error cell cover: `M'(m) ≥ 0` for all `m ∈ [2^95, Sc-46]`,
composed from the 22 `checkCoverK` cells. -/
theorem errLt_nonneg {m : Int} (h1 : 39614081257132168796771975168 ≤ m) (h2 : m ≤ 56022770974786139918731938181) :
    0 ≤ evalPoly certErrLtLit m := by
  rcases Int.lt_or_le m (39690713995389999812980837314 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell00 m (by omega) (by omega)
  rcases Int.lt_or_le m (39730677041036699034014990826 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell01 m (by omega) (by omega)
  rcases Int.lt_or_le m (39751783327094435418800986830 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell02 m (by omega) (by omega)
  rcases Int.lt_or_le m (39763891854368929726387401070 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell03 m (by omega) (by omega)
  rcases Int.lt_or_le m (39774662295602570286662651220 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell04 m (by omega) (by omega)
  rcases Int.lt_or_le m (40679997165554683551591585807 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell05 m (by omega) (by omega)
  rcases Int.lt_or_le m (40924139963113827378389531693 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell06 m (by omega) (by omega)
  rcases Int.lt_or_le m (40994349676318877769223711475 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell07 m (by omega) (by omega)
  rcases Int.lt_or_le m (41043045905047721566882051165 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell08 m (by omega) (by omega)
  rcases Int.lt_or_le m (43074909657573168724990774475 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell09 m (by omega) (by omega)
  rcases Int.lt_or_le m (43447171544436788464147782267 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell10 m (by omega) (by omega)
  rcases Int.lt_or_le m (43575643795639300685954607736 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell11 m (by omega) (by omega)
  rcases Int.lt_or_le m (46777373364869912303362302353 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell12 m (by omega) (by omega)
  rcases Int.lt_or_le m (47278853413441676783280697546 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell13 m (by omega) (by omega)
  rcases Int.lt_or_le m (49441198747998157922924465950 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell14 m (by omega) (by omega)
  rcases Int.lt_or_le m (52208342513818930575475816108 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell15 m (by omega) (by omega)
  rcases Int.lt_or_le m (53036600108885143092541888944 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell16 m (by omega) (by omega)
  exact checkCoverK_sound _ _ _ _ _ errLt_cell17 m (by omega) h2

end LnFloorCert

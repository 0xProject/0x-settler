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
import LnProof.ErrCertLtC18
import LnProof.ErrCertLtC19
import LnProof.ErrCertLtC20
import LnProof.ErrCertLtC21

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

/-- The lt-branch error cell cover: `M'(m) ≥ 0` for all `m ∈ [2^95, Sc-46]`,
composed from the 22 `checkCoverK` cells. -/
theorem errLt_nonneg {m : Int}
    (h1 : 39614081257132168796771975168 ≤ m)
    (h2 : m ≤ 56022770974786139918731938181) :
    0 ≤ evalPoly certErrLtLit m := by
  rcases Int.lt_or_le m (39690487033155318831492514644 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell00 m (by omega) (by omega)
  rcases Int.lt_or_le m (39730041034935017909079144467 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell01 m (by omega) (by omega)
  rcases Int.lt_or_le m (39750332389280211543769847732 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell02 m (by omega) (by omega)
  rcases Int.lt_or_le m (39760668564320063520044754512 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell03 m (by omega) (by omega)
  rcases Int.lt_or_le m (39765961139795848653992550332 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell04 m (by omega) (by omega)
  rcases Int.lt_or_le m (39768794545599430872698185558 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell05 m (by omega) (by omega)
  rcases Int.lt_or_le m (39770663872413954292287692847 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell06 m (by omega) (by omega)
  rcases Int.lt_or_le m (39776734234069348046975027352 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell07 m (by omega) (by omega)
  rcases Int.lt_or_le m (40679522109640282356488826987 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell08 m (by omega) (by omega)
  rcases Int.lt_or_le m (40921604216002285725209949214 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell09 m (by omega) (by omega)
  rcases Int.lt_or_le m (40987649777297210133226675106 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell10 m (by omega) (by omega)
  rcases Int.lt_or_le m (41021199587189415288102588115 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell11 m (by omega) (by omega)
  rcases Int.lt_or_le m (41120594256801000951027113788 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell12 m (by omega) (by omega)
  rcases Int.lt_or_le m (43087646344191582790285854567 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell13 m (by omega) (by omega)
  rcases Int.lt_or_le m (43441958359528469510743996388 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell14 m (by omega) (by omega)
  rcases Int.lt_or_le m (43550321627651620471295348779 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell15 m (by omega) (by omega)
  rcases Int.lt_or_le m (46772661970268323857756182433 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell16 m (by omega) (by omega)
  rcases Int.lt_or_le m (47265409858234429269501593572 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell17 m (by omega) (by omega)
  rcases Int.lt_or_le m (47863312455617981068416176220 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell18 m (by omega) (by omega)
  rcases Int.lt_or_le m (51996533350514057035622956906 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell19 m (by omega) (by omega)
  rcases Int.lt_or_le m (52718050121226925508670314994 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errLt_cell20 m (by omega) (by omega)
  exact checkCoverK_sound _ _ _ _ _ errLt_cell21 m (by omega) h2

end LnFloorCert

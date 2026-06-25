import LnProof.ErrCertGeC00
import LnProof.ErrCertGeC01
import LnProof.ErrCertGeC02
import LnProof.ErrCertGeC03
import LnProof.ErrCertGeC04
import LnProof.ErrCertGeC05
import LnProof.ErrCertGeC06
import LnProof.ErrCertGeC07
import LnProof.ErrCertGeC08
import LnProof.ErrCertGeC09
import LnProof.ErrCertGeC10
import LnProof.ErrCertGeC11
import LnProof.ErrCertGeC12
import LnProof.ErrCertGeC13
import LnProof.ErrCertGeC14

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

/-- The ge-branch error cell cover: `M'(m) ≥ 0` for all `m ∈ [Sc+46, MHI-1]`,
composed from the 17 `checkCoverK` cells. -/
theorem errGe_nonneg {m : Int} (h1 : 56022770974786139918731938273 ≤ m) (h2 : m ≤ 79228162514264337593543950335) :
    0 ≤ evalPoly certErrGeLit m := by
  rcases Int.lt_or_le m (62240135811560208137865971482 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errGe_cell00 m (by omega) (by omega)
  rcases Int.lt_or_le m (63000796656518944161749483048 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errGe_cell01 m (by omega) (by omega)
  rcases Int.lt_or_le m (63425726531882452517671634537 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errGe_cell02 m (by omega) (by omega)
  rcases Int.lt_or_le m (68520601063356091078894418602 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errGe_cell03 m (by omega) (by omega)
  rcases Int.lt_or_le m (69177516330888078974756550732 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errGe_cell04 m (by omega) (by omega)
  rcases Int.lt_or_le m (69402331473388570025030861838 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errGe_cell05 m (by omega) (by omega)
  rcases Int.lt_or_le m (73730515843223541190152991237 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errGe_cell06 m (by omega) (by omega)
  rcases Int.lt_or_le m (74334604836325087960096058977 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errGe_cell07 m (by omega) (by omega)
  rcases Int.lt_or_le m (74478977508043445090363886840 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errGe_cell08 m (by omega) (by omega)
  rcases Int.lt_or_le m (74922450207405969458838387098 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errGe_cell09 m (by omega) (by omega)
  rcases Int.lt_or_le m (77498269107963454383074120902 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errGe_cell10 m (by omega) (by omega)
  rcases Int.lt_or_le m (77862472582514100371703091044 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errGe_cell11 m (by omega) (by omega)
  rcases Int.lt_or_le m (77949071289735361475558199408 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errGe_cell12 m (by omega) (by omega)
  rcases Int.lt_or_le m (78001244224800080662875464165 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errGe_cell13 m (by omega) (by omega)
  exact checkCoverK_sound _ _ _ _ _ errGe_cell14 m (by omega) h2

end LnFloorCert

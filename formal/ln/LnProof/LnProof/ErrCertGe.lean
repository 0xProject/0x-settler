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
import LnProof.ErrCertGeC15
import LnProof.ErrCertGeC16

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

/-- The ge-branch error cell cover: `M'(m) ≥ 0` for all `m ∈ [Sc+46, MHI-1]`,
composed from the 17 `checkCoverK` cells. -/
theorem errGe_nonneg {m : Int}
    (h1 : 56022770974786139918731938273 ≤ m)
    (h2 : m ≤ 79228162514264337593543950335) :
    0 ≤ evalPoly certErrGeLit m := by
  rcases Int.lt_or_le m (62235000306952571703781716893 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errGe_cell00 m (by omega) (by omega)
  rcases Int.lt_or_le m (62976353586526539109099492225 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errGe_cell01 m (by omega) (by omega)
  rcases Int.lt_or_le m (63240749540139122990169033120 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errGe_cell02 m (by omega) (by omega)
  rcases Int.lt_or_le m (68486183181351891943137631147 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errGe_cell03 m (by omega) (by omega)
  rcases Int.lt_or_le m (69150385520028080205898383827 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errGe_cell04 m (by omega) (by omega)
  rcases Int.lt_or_le m (69318984104385194428820826876 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errGe_cell05 m (by omega) (by omega)
  rcases Int.lt_or_le m (73722346224426468943313592760 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errGe_cell06 m (by omega) (by omega)
  rcases Int.lt_or_le m (74321545568138162293005832386 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errGe_cell07 m (by omega) (by omega)
  rcases Int.lt_or_le m (74445984601364202409568704861 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errGe_cell08 m (by omega) (by omega)
  rcases Int.lt_or_le m (74523753466302552435307247886 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errGe_cell09 m (by omega) (by omega)
  rcases Int.lt_or_le m (77442057038427372518395562865 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errGe_cell10 m (by omega) (by omega)
  rcases Int.lt_or_le m (77852846065527338130569252120 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errGe_cell11 m (by omega) (by omega)
  rcases Int.lt_or_le m (77935952197004339716648454441 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errGe_cell12 m (by omega) (by omega)
  rcases Int.lt_or_le m (77969489922568434205266494789 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errGe_cell13 m (by omega) (by omega)
  rcases Int.lt_or_le m (77989822678558353447718470814 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errGe_cell14 m (by omega) (by omega)
  rcases Int.lt_or_le m (78082016047349163698545554608 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ errGe_cell15 m (by omega) (by omega)
  exact checkCoverK_sound _ _ _ _ _ errGe_cell16 m (by omega) h2

end LnFloorCert

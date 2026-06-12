import LnProof.FloorCertDefs
import LnProof.FloorCertLit

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geTN2b_eq_lit : geTN2b = geTN2bLit := by
  decide +kernel

theorem geTD2b_eq_lit : geTD2b = geTD2bLit := by
  decide +kernel

theorem geLo_eq_lit : certGeLo = certGeLoLit := by
  unfold certGeLo
  rw [geTN2b_eq_lit, geTD2b_eq_lit]
  decide +kernel

theorem geLo_chunk0 : checkCoverM certGeLoLit 14341829369545251819195376186275 16051397369545251819195376186277
    [921600000000000000000000000000, 414720000000000000000000000000, 373248000000000000000000000000] = true := by
  decide +kernel

theorem geLo_chunk1 : checkCoverM certGeLoLit 16051397369545251819195376186278 18241616633545251819195376186280
    [1343692800000000000000000000000, 302330880000000000000000000000, 544195584000000000000000000000] = true := by
  decide +kernel

theorem geLo_chunk2 : checkCoverM certGeLoLit 18241616633545251819195376186281 19348510451401251819195376186283
    [489776025600000000000000000000, 220399211520000000000000000000, 396718580736000000000000000000] = true := by
  decide +kernel

theorem geLo_chunk3 : checkCoverM certGeLoLit 19348510451401251819195376186284 19952161587712529772726802791418
    [357046722662400000000000000000, 129791796657304186069171897438, 116812616991573767462254707694] = true := by
  decide +kernel

theorem geLo_chunk4 : checkCoverM certGeLoLit 19952161587712529772726802791419 20282409603651670423947251286015
    [330248015939140651220448494596] = true := by
  decide +kernel

theorem geLo_nonneg {m : Int} (h1 : 14341829369545251819195376186275 ≤ m) (h2 : m ≤ 20282409603651670423947251286015) :
    0 ≤ evalPoly certGeLo m := by
  rw [geLo_eq_lit]
  rcases Int.lt_or_le m (16051397369545251819195376186277 + 1) with h | h
  · exact checkCoverM_sound _ _ _ _ geLo_chunk0 m (by omega) (by omega)
  rcases Int.lt_or_le m (18241616633545251819195376186280 + 1) with h | h
  · exact checkCoverM_sound _ _ _ _ geLo_chunk1 m (by omega) (by omega)
  rcases Int.lt_or_le m (19348510451401251819195376186283 + 1) with h | h
  · exact checkCoverM_sound _ _ _ _ geLo_chunk2 m (by omega) (by omega)
  rcases Int.lt_or_le m (19952161587712529772726802791418 + 1) with h | h
  · exact checkCoverM_sound _ _ _ _ geLo_chunk3 m (by omega) (by omega)
  exact checkCoverM_sound _ _ _ _ geLo_chunk4 m (by omega) h2

end LnFloorCert

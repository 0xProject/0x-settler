import LnProof.FloorCertDefs
import LnProof.FloorCertLit

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_eq_lit : certGeUp = certGeUpLit := by
  decide +kernel

theorem geUp_chunk0 : checkCoverM certGeUpLit 14341829369545251819195376186275 16378565369545251819195376186277
    [460800000000000000000000000000, 829440000000000000000000000000, 746496000000000000000000000000] = true := by
  decide +kernel

theorem geUp_chunk1 : checkCoverM certGeUpLit 16378565369545251819195376186278 17863345913545251819195376186280
    [335923200000000000000000000000, 604661760000000000000000000000, 544195584000000000000000000000] = true := by
  decide +kernel

theorem geUp_chunk2 : checkCoverM certGeUpLit 17863345913545251819195376186281 19470449219371196005264548083722
    [489776025600000000000000000000, 881596846080000000000000000000, 235730434145944186069171897439] = true := by
  decide +kernel

theorem geUp_chunk3 : checkCoverM certGeUpLit 19470449219371196005264548083723 20162553774023688135563636774605
    [212157390731349767462254707695, 381883303316429581432058473851, 98063860604712781404775509334] = true := by
  decide +kernel

theorem geUp_chunk4 : checkCoverM certGeUpLit 20162553774023688135563636774606 20282409603651670423947251286015
    [53935123332592029772626530133, 65920706295390258610987981275] = true := by
  decide +kernel

theorem geUp_nonneg {m : Int} (h1 : 14341829369545251819195376186275 ≤ m) (h2 : m ≤ 20282409603651670423947251286015) :
    0 ≤ evalPoly certGeUp m := by
  rw [geUp_eq_lit]
  rcases Int.lt_or_le m (16378565369545251819195376186277 + 1) with h | h
  · exact checkCoverM_sound _ _ _ _ geUp_chunk0 m (by omega) (by omega)
  rcases Int.lt_or_le m (17863345913545251819195376186280 + 1) with h | h
  · exact checkCoverM_sound _ _ _ _ geUp_chunk1 m (by omega) (by omega)
  rcases Int.lt_or_le m (19470449219371196005264548083722 + 1) with h | h
  · exact checkCoverM_sound _ _ _ _ geUp_chunk2 m (by omega) (by omega)
  rcases Int.lt_or_le m (20162553774023688135563636774605 + 1) with h | h
  · exact checkCoverM_sound _ _ _ _ geUp_chunk3 m (by omega) (by omega)
  exact checkCoverM_sound _ _ _ _ geUp_chunk4 m (by omega) h2

end LnFloorCert

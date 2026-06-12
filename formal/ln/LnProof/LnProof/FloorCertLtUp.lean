import LnProof.FloorCertDefs
import LnProof.FloorCertLit

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltTN2b_eq_lit : ltTN2b = ltTN2bLit := by
  decide +kernel

theorem ltTD2b_eq_lit : ltTD2b = ltTD2bLit := by
  decide +kernel

theorem ltUp_eq_lit : certLtUp = certLtUpLit := by
  unfold certLtUp
  rw [ltTN2b_eq_lit, ltTD2b_eq_lit]
  decide +kernel

theorem ltUp_chunk0 : checkCoverM certLtUpLit 10141204801825835211973625643008 10297300801825835211973625643010
    [57600000000000000000000000000, 51840000000000000000000000000, 46656000000000000000000000000] = true := by
  decide +kernel

theorem ltUp_chunk1 : checkCoverM certLtUpLit 10297300801825835211973625643011 10844855617825835211973625643013
    [335923200000000000000000000000, 75582720000000000000000000000, 136048896000000000000000000000] = true := by
  decide +kernel

theorem ltUp_chunk2 : checkCoverM certLtUpLit 10844855617825835211973625643014 12348468016417835211973625643016
    [489776025600000000000000000000, 220399211520000000000000000000, 793437161472000000000000000000] = true := by
  decide +kernel

theorem ltUp_chunk3 : checkCoverM certLtUpLit 12348468016417835211973625643017 14341829369545251819195376186183
    [357046722662400000000000000000, 1636314630465016607221750543165] = true := by
  decide +kernel

theorem ltUp_nonneg {m : Int} (h1 : 10141204801825835211973625643008 ≤ m) (h2 : m ≤ 14341829369545251819195376186183) :
    0 ≤ evalPoly certLtUp m := by
  rw [ltUp_eq_lit]
  rcases Int.lt_or_le m (10297300801825835211973625643010 + 1) with h | h
  · exact checkCoverM_sound _ _ _ _ ltUp_chunk0 m (by omega) (by omega)
  rcases Int.lt_or_le m (10844855617825835211973625643013 + 1) with h | h
  · exact checkCoverM_sound _ _ _ _ ltUp_chunk1 m (by omega) (by omega)
  rcases Int.lt_or_le m (12348468016417835211973625643016 + 1) with h | h
  · exact checkCoverM_sound _ _ _ _ ltUp_chunk2 m (by omega) (by omega)
  exact checkCoverM_sound _ _ _ _ ltUp_chunk3 m (by omega) h2

end LnFloorCert

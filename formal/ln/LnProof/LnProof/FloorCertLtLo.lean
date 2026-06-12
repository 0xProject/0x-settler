import LnProof.FloorCertDefs
import LnProof.FloorCertLit

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltTN_eq_lit : ltTN = ltTNLit := by
  decide +kernel

theorem ltTD_eq_lit : ltTD = ltTDLit := by
  decide +kernel

theorem ltLo_eq_lit : certLtLo = certLtLoLit := by
  unfold certLtLo
  rw [ltTN_eq_lit, ltTD_eq_lit]
  decide +kernel

theorem ltLo_chunk0 : checkCoverM certLtLoLit 10141204801825835211973625643008 10180228801825835211973625643010
    [14400000000000000000000000000, 12960000000000000000000000000, 11664000000000000000000000000] = true := by
  decide +kernel

theorem ltLo_chunk1 : checkCoverM certLtLoLit 10180228801825835211973625643011 10491797569825835211973625643013
    [167961600000000000000000000000, 75582720000000000000000000000, 68024448000000000000000000000] = true := by
  decide +kernel

theorem ltLo_chunk2 : checkCoverM certLtLoLit 10491797569825835211973625643014 11885210362657835211973625643016
    [489776025600000000000000000000, 110199605760000000000000000000, 793437161472000000000000000000] = true := by
  decide +kernel

theorem ltLo_chunk3 : checkCoverM certLtLoLit 11885210362657835211973625643017 13463356876825643211973625643019
    [357046722662400000000000000000, 642684100792320000000000000000, 578415690713088000000000000000] = true := by
  decide +kernel

theorem ltLo_chunk4 : checkCoverM certLtLoLit 13463356876825643211973625643020 14341829369545251819195376186183
    [878472492719608607221750543163] = true := by
  decide +kernel

theorem ltLo_nonneg {m : Int} (h1 : 10141204801825835211973625643008 ≤ m) (h2 : m ≤ 14341829369545251819195376186183) :
    0 ≤ evalPoly certLtLo m := by
  rw [ltLo_eq_lit]
  rcases Int.lt_or_le m (10180228801825835211973625643010 + 1) with h | h
  · exact checkCoverM_sound _ _ _ _ ltLo_chunk0 m (by omega) (by omega)
  rcases Int.lt_or_le m (10491797569825835211973625643013 + 1) with h | h
  · exact checkCoverM_sound _ _ _ _ ltLo_chunk1 m (by omega) (by omega)
  rcases Int.lt_or_le m (11885210362657835211973625643016 + 1) with h | h
  · exact checkCoverM_sound _ _ _ _ ltLo_chunk2 m (by omega) (by omega)
  rcases Int.lt_or_le m (13463356876825643211973625643019 + 1) with h | h
  · exact checkCoverM_sound _ _ _ _ ltLo_chunk3 m (by omega) (by omega)
  exact checkCoverM_sound _ _ _ _ ltLo_chunk4 m (by omega) h2

end LnFloorCert

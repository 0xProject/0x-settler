import LnProof.FloorCertDefs

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geH_check : checkCover certGeH 14341829369545251819195376186275 20282409603651670423947251286015
    [5940580234106418604751875099740] = true := by
  decide +kernel

theorem geH_nonneg {m : Int} (h1 : 14341829369545251819195376186275 ≤ m) (h2 : m ≤ 20282409603651670423947251286015) :
    0 ≤ evalPoly certGeH m :=
  checkCover_sound _ _ _ _ geH_check m h1 h2

theorem ltH_check : checkCover certLtH 10141204801825835211973625643008 14341829369545251819195376186183
    [4200624567719416607221750543175] = true := by
  decide +kernel

theorem ltH_nonneg {m : Int} (h1 : 10141204801825835211973625643008 ≤ m) (h2 : m ≤ 14341829369545251819195376186183) :
    0 ≤ evalPoly certLtH m :=
  checkCover_sound _ _ _ _ ltH_check m h1 h2

theorem geTD_check : checkCover certGeTD 14341829369545251819195376186275 20282409603651670423947251286015
    [5940580234106418604751875099740] = true := by
  decide +kernel

theorem geTD_nonneg {m : Int} (h1 : 14341829369545251819195376186275 ≤ m) (h2 : m ≤ 20282409603651670423947251286015) :
    0 ≤ evalPoly certGeTD m :=
  checkCover_sound _ _ _ _ geTD_check m h1 h2

theorem geTD2_check : checkCover certGeTD2 14341829369545251819195376186275 20282409603651670423947251286015
    [5940580234106418604751875099740] = true := by
  decide +kernel

theorem geTD2_nonneg {m : Int} (h1 : 14341829369545251819195376186275 ≤ m) (h2 : m ≤ 20282409603651670423947251286015) :
    0 ≤ evalPoly certGeTD2 m :=
  checkCover_sound _ _ _ _ geTD2_check m h1 h2

theorem ltTD_check : checkCover certLtTD 10141204801825835211973625643008 14341829369545251819195376186183
    [4200624567719416607221750543175] = true := by
  decide +kernel

theorem ltTD_nonneg {m : Int} (h1 : 10141204801825835211973625643008 ≤ m) (h2 : m ≤ 14341829369545251819195376186183) :
    0 ≤ evalPoly certLtTD m :=
  checkCover_sound _ _ _ _ ltTD_check m h1 h2

theorem ltTD2_check : checkCover certLtTD2 10141204801825835211973625643008 14341829369545251819195376186183
    [4200624567719416607221750543175] = true := by
  decide +kernel

theorem ltTD2_nonneg {m : Int} (h1 : 10141204801825835211973625643008 ≤ m) (h2 : m ≤ 14341829369545251819195376186183) :
    0 ≤ evalPoly certLtTD2 m :=
  checkCover_sound _ _ _ _ ltTD2_check m h1 h2

theorem geTN_check : checkCover geTN 14341829369545251819195376186275 20282409603651670423947251286015
    [5940580234106418604751875099740] = true := by
  decide +kernel

theorem geTN_nonneg {m : Int} (h1 : 14341829369545251819195376186275 ≤ m) (h2 : m ≤ 20282409603651670423947251286015) :
    0 ≤ evalPoly geTN m :=
  checkCover_sound _ _ _ _ geTN_check m h1 h2

theorem geTN2_check : checkCover geTN2b 14341829369545251819195376186275 20282409603651670423947251286015
    [5940580234106418604751875099740] = true := by
  decide +kernel

theorem geTN2_nonneg {m : Int} (h1 : 14341829369545251819195376186275 ≤ m) (h2 : m ≤ 20282409603651670423947251286015) :
    0 ≤ evalPoly geTN2b m :=
  checkCover_sound _ _ _ _ geTN2_check m h1 h2

theorem ltTN_check : checkCover ltTN 10141204801825835211973625643008 14341829369545251819195376186183
    [4200624567719416607221750543175] = true := by
  decide +kernel

theorem ltTN_nonneg {m : Int} (h1 : 10141204801825835211973625643008 ≤ m) (h2 : m ≤ 14341829369545251819195376186183) :
    0 ≤ evalPoly ltTN m :=
  checkCover_sound _ _ _ _ ltTN_check m h1 h2

theorem ltTN2_check : checkCover ltTN2b 10141204801825835211973625643008 14341829369545251819195376186183
    [4200624567719416607221750543175] = true := by
  decide +kernel

theorem ltTN2_nonneg {m : Int} (h1 : 10141204801825835211973625643008 ≤ m) (h2 : m ≤ 14341829369545251819195376186183) :
    0 ≤ evalPoly ltTN2b m :=
  checkCover_sound _ _ _ _ ltTN2_check m h1 h2

theorem geWS_check : checkCover certGeWS 14341829369545251819195376186275 20282409603651670423947251286015
    [5940580234106418604751875099740] = true := by
  decide +kernel

theorem geWS_nonneg {m : Int} (h1 : 14341829369545251819195376186275 ≤ m) (h2 : m ≤ 20282409603651670423947251286015) :
    0 ≤ evalPoly certGeWS m :=
  checkCover_sound _ _ _ _ geWS_check m h1 h2

theorem ltWS_check : checkCover certLtWS 10141204801825835211973625643008 14341829369545251819195376186183
    [4200624567719416607221750543175] = true := by
  decide +kernel

theorem ltWS_nonneg {m : Int} (h1 : 10141204801825835211973625643008 ≤ m) (h2 : m ≤ 14341829369545251819195376186183) :
    0 ≤ evalPoly certLtWS m :=
  checkCover_sound _ _ _ _ ltWS_check m h1 h2

end LnFloorCert

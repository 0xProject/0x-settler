import LnProof.Floor.CertDefs

namespace LnFloorCert
open Common.Poly

set_option maxRecDepth 100000

theorem ltH_check : checkCover certLtH 39614081257132168796771975168 56022770974786139918731938181
    [16408689717653971121959963013] = true := by
  decide +kernel

theorem ltH_nonneg {m : Int} (h1 : 39614081257132168796771975168 ≤ m) (h2 : m ≤ 56022770974786139918731938181) :
    0 ≤ evalPoly certLtH m :=
  checkCover_sound _ _ _ _ ltH_check m h1 h2

theorem geTD2_check : checkCover certGeTD2 56022770974786139918731938273 79228162514264337593543950335
    [23205391539478197674812012062] = true := by
  decide +kernel

theorem geTD2_nonneg {m : Int} (h1 : 56022770974786139918731938273 ≤ m) (h2 : m ≤ 79228162514264337593543950335) :
    0 ≤ evalPoly certGeTD2 m :=
  checkCover_sound _ _ _ _ geTD2_check m h1 h2

theorem ltTD_check : checkCover certLtTD 39614081257132168796771975168 56022770974786139918731938181
    [16408689717653971121959963013] = true := by
  decide +kernel

theorem ltTD_nonneg {m : Int} (h1 : 39614081257132168796771975168 ≤ m) (h2 : m ≤ 56022770974786139918731938181) :
    0 ≤ evalPoly certLtTD m :=
  checkCover_sound _ _ _ _ ltTD_check m h1 h2

theorem ltTD2_check : checkCover certLtTD2 39614081257132168796771975168 56022770974786139918731938181
    [16408689717653971121959963013] = true := by
  decide +kernel

theorem ltTD2_nonneg {m : Int} (h1 : 39614081257132168796771975168 ≤ m) (h2 : m ≤ 56022770974786139918731938181) :
    0 ≤ evalPoly certLtTD2 m :=
  checkCover_sound _ _ _ _ ltTD2_check m h1 h2

theorem geTN2_check : checkCover geTN2b 56022770974786139918731938273 79228162514264337593543950335
    [23205391539478197674812012062] = true := by
  decide +kernel

theorem geTN2_nonneg {m : Int} (h1 : 56022770974786139918731938273 ≤ m) (h2 : m ≤ 79228162514264337593543950335) :
    0 ≤ evalPoly geTN2b m :=
  checkCover_sound _ _ _ _ geTN2_check m h1 h2

theorem ltTN_check : checkCover ltTN 39614081257132168796771975168 56022770974786139918731938181
    [16408689717653971121959963013] = true := by
  decide +kernel

theorem ltTN_nonneg {m : Int} (h1 : 39614081257132168796771975168 ≤ m) (h2 : m ≤ 56022770974786139918731938181) :
    0 ≤ evalPoly ltTN m :=
  checkCover_sound _ _ _ _ ltTN_check m h1 h2

theorem ltTN2_check : checkCover ltTN2b 39614081257132168796771975168 56022770974786139918731938181
    [16408689717653971121959963013] = true := by
  decide +kernel

theorem ltTN2_nonneg {m : Int} (h1 : 39614081257132168796771975168 ≤ m) (h2 : m ≤ 56022770974786139918731938181) :
    0 ≤ evalPoly ltTN2b m :=
  checkCover_sound _ _ _ _ ltTN2_check m h1 h2

theorem geWS_check : checkCover certGeWS 56022770974786139918731938273 79228162514264337593543950335
    [23205391539478197674812012062] = true := by
  decide +kernel

theorem geWS_nonneg {m : Int} (h1 : 56022770974786139918731938273 ≤ m) (h2 : m ≤ 79228162514264337593543950335) :
    0 ≤ evalPoly certGeWS m :=
  checkCover_sound _ _ _ _ geWS_check m h1 h2

theorem ltWS_check : checkCover certLtWS 39614081257132168796771975168 56022770974786139918731938181
    [16408689717653971121959963013] = true := by
  decide +kernel

theorem ltWS_nonneg {m : Int} (h1 : 39614081257132168796771975168 ≤ m) (h2 : m ≤ 56022770974786139918731938181) :
    0 ≤ evalPoly certLtWS m :=
  checkCover_sound _ _ _ _ ltWS_check m h1 h2

end LnFloorCert

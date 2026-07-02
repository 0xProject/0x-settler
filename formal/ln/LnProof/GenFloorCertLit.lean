import LnProof.Floor.CertDefs
import Common.GenCover

open LnFloorCert Common.GenCover

namespace GenFloorCertLit

def fileText : String :=
  "/-! Literal coefficient lists for the floor certificate polynomials. -/\n\n" ++
    "namespace LnFloorCert\n\n" ++
    litText "geTNLit" geTN ++
    litText "geTDLit" geTD ++
    litText "geTN2bLit" geTN2b ++
    litText "geTD2bLit" geTD2b ++
    litText "ltTNLit" ltTN ++
    litText "ltTDLit" ltTD ++
    litText "ltTN2bLit" ltTN2b ++
    litText "ltTD2bLit" ltTD2b ++
    litText "certGeUpLit" (ptrim certGeUp) ++
    litText "certGeLoLit" (ptrim certGeLo) ++
    litText "certLtUpLit" (ptrim certLtUp) ++
    litText "certLtLoLit" (ptrim certLtLo) ++
    "end LnFloorCert\n"

end GenFloorCertLit

#eval IO.FS.writeFile "LnProof/Cert/FloorCertLit.lean" GenFloorCertLit.fileText

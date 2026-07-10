import LnProof.Floor.CertDefs
import Common.GenCover

open LnFloorCert Common.GenCover

namespace GenFloorCertLit

def fileText (body : String) : String :=
  "/-! Literal coefficient lists for one floor-certificate family. -/\n\n" ++
    "namespace LnFloorCert\n\n" ++
    body ++
    "end LnFloorCert\n"

def geUpText : String := fileText <|
    litText "geTNLit" geTN ++
    litText "geTDLit" geTD ++
    litText "certGeUpLit" (ptrim certGeUp)

def geLoText : String := fileText <|
    litText "geTN2bLit" geTN2b ++
    litText "geTD2bLit" geTD2b ++
    litText "certGeLoLit" (ptrim certGeLo)

def ltUpText : String := fileText <|
    litText "ltTN2bLit" ltTN2b ++
    litText "ltTD2bLit" ltTD2b ++
    litText "certLtUpLit" (ptrim certLtUp)

def ltLoText : String := fileText <|
    litText "ltTNLit" ltTN ++
    litText "ltTDLit" ltTD ++
    litText "certLtLoLit" (ptrim certLtLo)

end GenFloorCertLit

#eval do
  reconcileOutputs "LnProof/Cert"
    ["FloorCertLit", "FloorCertGeUpLit", "FloorCertGeLoLit", "FloorCertLtUpLit",
      "FloorCertLtLoLit"]
    ["FloorCertGeUpLit.lean", "FloorCertGeLoLit.lean", "FloorCertLtUpLit.lean",
      "FloorCertLtLoLit.lean"]
  IO.FS.writeFile "LnProof/Cert/FloorCertGeUpLit.lean" GenFloorCertLit.geUpText
  IO.FS.writeFile "LnProof/Cert/FloorCertGeLoLit.lean" GenFloorCertLit.geLoText
  IO.FS.writeFile "LnProof/Cert/FloorCertLtUpLit.lean" GenFloorCertLit.ltUpText
  IO.FS.writeFile "LnProof/Cert/FloorCertLtLoLit.lean" GenFloorCertLit.ltLoText

import LnProof.Floor.CertDefs
import Common.GenCover

open LnFloorCert Common.GenCover

namespace GenFloorCertLit

def fileText (body : String) : String :=
  "/-! Literal coefficient lists for one floor-certificate family. -/\n\n" ++
    "namespace LnFloorCert\n\n" ++
    body ++
    "end LnFloorCert\n"

def geLoText : String := fileText <|
    litText "geTN2bLit" geTN2b ++
    litText "geTD2bLit" geTD2b ++
    litText "certGeLoLit" (ptrim certGeLo)

def ltLoText : String := fileText <|
    litText "ltTNLit" ltTN ++
    litText "ltTDLit" ltTD ++
    litText "certLtLoLit" (ptrim certLtLo)

end GenFloorCertLit

#eval do
  reconcileOutputs "LnProof/Cert"
    ["FloorCertGeLoLit", "FloorCertLtLoLit"]
    ["FloorCertGeLoLit.lean", "FloorCertLtLoLit.lean"]
  IO.FS.writeFile "LnProof/Cert/FloorCertGeLoLit.lean" GenFloorCertLit.geLoText
  IO.FS.writeFile "LnProof/Cert/FloorCertLtLoLit.lean" GenFloorCertLit.ltLoText

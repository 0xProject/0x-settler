import LnProof.Floor.CertDefs

open LnFloorCert

namespace GenFloorCertLit

def ptrim (a : List Int) : List Int :=
  let r := (a.reverse.dropWhile (· == 0)).reverse
  if r.isEmpty then [0] else r

def litDef (name : String) (coeffs : List Int) : String :=
  "def " ++ name ++ " : List Int := [\n  " ++
    String.intercalate ",\n  " (coeffs.map toString) ++ "]\n\n"

def litText : String :=
  "/-! Literal coefficient lists for the floor certificate polynomials. -/\n\n" ++
    "namespace LnFloorCert\n\n" ++
    litDef "geTNLit" geTN ++
    litDef "geTDLit" geTD ++
    litDef "geTN2bLit" geTN2b ++
    litDef "geTD2bLit" geTD2b ++
    litDef "ltTNLit" ltTN ++
    litDef "ltTDLit" ltTD ++
    litDef "ltTN2bLit" ltTN2b ++
    litDef "ltTD2bLit" ltTD2b ++
    litDef "certGeUpLit" (ptrim certGeUp) ++
    litDef "certGeLoLit" (ptrim certGeLo) ++
    litDef "certLtUpLit" (ptrim certLtUp) ++
    litDef "certLtLoLit" (ptrim certLtLo) ++
    "end LnFloorCert\n"

end GenFloorCertLit

#eval IO.FS.writeFile "LnProof/Cert/FloorCertLit.lean" GenFloorCertLit.litText

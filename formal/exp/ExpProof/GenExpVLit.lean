import ExpProof.Floor.CertDefsV
import ExpProof.Floor.GranPieces
import Common.Foundation.KroneckerShift
import Common.GenCover

/-!
# Cert literal + cover generator for the **v-form** reduced-argument Taylor caps

Computes the never-over (`certExpUp`) and not-two-below (`certExpLo`) v-form certificate polynomials
from the symbolic `ExpCertV` definitions, emits the building-block + cert literal coefficient lists
(`Cert/ExpVCertLit.lean`), then greedily walks `[0, H128]` for each — exactly the predicate the
in-kernel `checkCoverK` decides — and writes one `Cert/ExpV{Up,Lo,…}C<NN>.lean` cell file per sub-cell
plus the cover module with the symbolic-cert↔literal equality and the `_nonneg` ladder.

Run with `lake env lean GenExpVLit.lean` after
`lake build ExpProof.Floor.CertDefsV ExpProof.Floor.GranPieces Common.GenCover`. Output is
deterministic (byte-identical on re-run). Only the generated `Cert/ExpV*` files are machine
output; this
generator, the hand-written `Floor/CertDefsV.lean` symbolic definitions, and the
`Floor/GranPieces.lean` piece table are tracked.
-/

open Common.Poly ExpCertV Common.GenCover

namespace GenExpVLit

/-- Walk `[lo, hi]`, write one cell file per sub-cell, then write the cover module. -/
def emit (litName coverMod modPrefix cellPrefix certEqName litNonneg symNonneg symName eqTac : String)
    (C : List Int) (lo hi : Int) : IO Unit := do
  let (ok, cells) := walk C lo hi
  IO.println s!"-- {coverMod}: reached={ok} ncells={cells.length}"
  if ! ok then IO.println s!"-- FAILED tail: {cells.drop (cells.length - 2)}"; return
  for (aw, i) in cells.zipIdx do
    let (a, w) := aw
    IO.FS.writeFile s!"ExpProof/Cert/{modPrefix}{pad2 i}.lean"
      (cellText "ExpProof.Cert.ExpVCertLit" "ExpCertV" s!"{cellPrefix}{pad2 i}" litName a w)
  let lb := "{"; let rb := "}"
  let mut s := "import ExpProof.Floor.CertDefsV\nimport ExpProof.Cert.ExpVCertLit\nimport Common.Foundation.KroneckerShift\n"
  for (_, i) in cells.zipIdx do s := s ++ s!"import ExpProof.Cert.{modPrefix}{pad2 i}\n"
  s := s ++ s!"\nnamespace ExpCertV\nopen Common.Poly\n\nset_option maxRecDepth 100000\n\n"
  s := s ++ s!"theorem {certEqName} : {symName} = {litName} := by\n{eqTac}\n\n"
  s := s ++ s!"theorem {litNonneg} {lb}t : Int{rb} (h1 : {lo} ≤ t) (h2 : t ≤ {hi}) :\n"
  s := s ++ s!"    0 ≤ evalPoly {litName} t := by\n"
  let n := cells.length
  for (aw, i) in cells.zipIdx do
    let (a, w) := aw
    s := s ++ ladderStep s!"{cellPrefix}{pad2 i}" "t" a w (i + 1 == n)
  s := s ++ s!"\ntheorem {symNonneg} {lb}t : Int{rb} (h1 : {lo} ≤ t) (h2 : t ≤ {hi}) :\n"
  s := s ++ s!"    0 ≤ evalPoly {symName} t := by\n  rw [{certEqName}]; exact {litNonneg} h1 h2\n"
  s := s ++ "\nend ExpCertV\n"
  IO.FS.writeFile s!"ExpProof/Cert/{coverMod}.lean" s

end GenExpVLit

open GenExpVLit

/-- Tactic block proving `certExpUp = certExpUpLit`. -/
def upEqTac : String :=
  "  have hy : yUB = yUBLit := by unfold yUB numExpV evNumVPoly todNumV odNumVPoly mulT2; decide +kernel\n" ++
  "  have hw : wUB = wUBLit := by unfold wUB denExpV evNumVPoly todNumV odNumVPoly mulT2; decide +kernel\n" ++
  "  have ht : tailUp = tailUpLit := by unfold tailUp expN27; decide +kernel\n" ++
  "  unfold certExpUp\n  rw [hy, hw, ht]\n  decide +kernel"

/-- Tactic block proving `certExpLo = certExpLoLit`. -/
def loEqTac : String :=
  "  have he : expN27 = expN27Lit := by unfold expN27; decide +kernel\n" ++
  "  have hy : yLB = yLBLit := by unfold yLB numExpV evNumVPoly todNumV odNumVPoly mulT2; decide +kernel\n" ++
  "  have hw : wLB = wLBLit := by unfold wLB denExpV evNumVPoly todNumV odNumVPoly mulT2; decide +kernel\n" ++
  "  unfold certExpLo\n  rw [he, hy, hw]\n  decide +kernel"

/-- Tactic block proving `numExpV = numExpVLit`. -/
def numEqTac : String :=
  "  unfold numExpV evNumVPoly todNumV odNumVPoly mulT2\n  decide +kernel"

/-- Tactic block proving `certDenM1 = certDenM1Lit`. -/
def denM1EqTac : String :=
  "  unfold certDenM1 denExpV evNumVPoly todNumV odNumVPoly mulT2\n  decide +kernel"

/-- Tactic block proving `certDOver = certDOverLit`. -/
def dOverEqTac : String :=
  "  unfold certDOver certDOverP evVPoly odVPoly\n  decide +kernel"

/-- Tactic block proving `certDOverP T D = certDOvP<NN>Lit`. -/
def dOverPEqTac : String :=
  "  unfold certDOverP evVPoly odVPoly\n  decide +kernel"

/-- Tactic block proving `certDUnderP T D = certDUnP<NN>Lit`. -/
def dUnderPEqTac : String :=
  "  unfold certDUnderP evVPoly odVPoly\n  decide +kernel"

#eval do
  let cUp := ptrim certExpUp
  let cLo := ptrim certExpLo
  let mut lits :=
    ("/-! Generated v-form cut-certificate literal coefficient lists. -/\n\nnamespace ExpCertV\n\n" ++
      litText "numExpVLit" (ptrim numExpV) ++
      litText "denExpVLit" (ptrim denExpV) ++
      litText "expN27Lit" (ptrim expN27) ++
      litText "tailUpLit" (ptrim tailUp) ++
      litText "yUBLit" (ptrim yUB) ++
      litText "wUBLit" (ptrim wUB) ++
      litText "yLBLit" (ptrim yLB) ++
      litText "wLBLit" (ptrim wLB) ++
      litText "certDenM1Lit" (ptrim certDenM1) ++
      litText "certExpUpLit" cUp ++
      litText "certExpLoLit" cLo ++
      litText "certDOverLit" (ptrim certDOver))
  for (p, i) in granPieces.zipIdx do
    let (_, _, t, dO, dU) := p
    lits := lits ++ litText s!"certDOvP{pad2 i}Lit" (ptrim (certDOverP t dO))
    lits := lits ++ litText s!"certDUnP{pad2 i}Lit" (ptrim (certDUnderP t dU))
  IO.FS.writeFile "ExpProof/Cert/ExpVCertLit.lean" (lits ++ "end ExpCertV\n")
  IO.println "v-form literals written"
  emit "certExpUpLit" "ExpVUp" "ExpVUpC" "expVUp_cell" "certExpUp_eq" "expVUpLit_nonneg"
    "expVUp_nonneg" "certExpUp" upEqTac cUp 0 (H129 : Int)
  emit "certExpLoLit" "ExpVLo" "ExpVLoC" "expVLo_cell" "certExpLo_eq" "expVLoLit_nonneg"
    "expVLo_nonneg" "certExpLo" loEqTac cLo 0 (H129 : Int)
  emit "numExpVLit" "ExpVNum" "ExpVNumC" "expVNum_cell" "numExpV_eq" "numExpVLit_nonneg"
    "numExpV_nonneg" "numExpV" numEqTac (ptrim numExpV) 0 (H129 : Int)
  emit "certDenM1Lit" "ExpVDenM1" "ExpVDenM1C" "expVDenM1_cell" "certDenM1_eq" "denM1VLit_nonneg"
    "denM1V_nonneg" "certDenM1" denM1EqTac (ptrim certDenM1) 0 (H129 : Int)
  emit "certDOverLit" "ExpVDOver" "ExpVDOverC" "expVDOver_cell" "certDOver_eq" "dOverVLit_nonneg"
    "dOverV_nonneg" "certDOver" dOverEqTac (ptrim certDOver) 0 ((vmaxV : Int) + 1)
  for (p, i) in granPieces.zipIdx do
    let (vlo, vhi, t, dO, dU) := p
    emit s!"certDOvP{pad2 i}Lit" s!"ExpVDOvP{pad2 i}" s!"ExpVDOvP{pad2 i}C" s!"dOvP{pad2 i}_cell"
      s!"certDOvP{pad2 i}_eq" s!"dOvP{pad2 i}Lit_nonneg" s!"dOvP{pad2 i}_nonneg"
      s!"(certDOverP {t} {dO})" dOverPEqTac (ptrim (certDOverP t dO)) vlo (vhi + 1)
    emit s!"certDUnP{pad2 i}Lit" s!"ExpVDUnP{pad2 i}" s!"ExpVDUnP{pad2 i}C" s!"dUnP{pad2 i}_cell"
      s!"certDUnP{pad2 i}_eq" s!"dUnP{pad2 i}Lit_nonneg" s!"dUnP{pad2 i}_nonneg"
      s!"(certDUnderP {t} {dU})" dUnderPEqTac (ptrim (certDUnderP t dU)) vlo (vhi + 1)

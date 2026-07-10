import ExpProof.Floor.CertDefsV
import ExpProof.Floor.GranPieces
import Common.GenBernstein

/-!
# Reduced-argument certificate generator

Taylor upper and lower bounds use exact Bernstein witnesses.  Numerator,
denominator, and granularity families use interval-Horner/Kronecker cells.
Each family owns a distinct literal module so an approximation change does
not invalidate unrelated certificate leaves.
-/

open Common.Poly ExpCertV Common.GenCover Common.GenBernstein

namespace GenExpVLit

def outDir : String := "ExpProof/Cert"

def literalText (body : String) : String :=
  "namespace ExpCertV\n\n" ++ body ++ "end ExpCertV\n"

def theoremLadder (cellPrefix x : String) (cells : List CellSpec) : String :=
  cells.zipIdx.foldl (fun text row =>
    let (cell, i) := row
    let name := s!"{cellPrefix}{pad2 i}_nonnegOn"
    if i + 1 = cells.length then
      text ++ s!"  exact {name} {x} (by omega) hhi\n"
    else
      text ++ s!"  rcases Int.lt_or_le {x} ({cell.hi} + 1) with h | h\n" ++
        s!"  · exact {name} {x} (by omega) (by omega)\n") ""

def coverText (literalImport coverImport ns litName certEqName litNonnegOn
    symNonnegOn pointwiseName symName eqTac cellPrefix : String)
    (lo hi : Int) (cells : List CellSpec) : String :=
  let imports := cells.zipIdx.foldl (fun text row =>
    let (_, i) := row
    text ++ s!"import ExpProof.Cert.{coverImport}{pad2 i}\n")
    s!"import ExpProof.Floor.CertDefsV\nimport {literalImport}\n"
  imports ++ s!"\nnamespace {ns}\n\nopen Common.Poly\n\nset_option maxRecDepth 100000\n\n" ++
    s!"theorem {certEqName} : {symName} = {litName} := by\n{eqTac}\n\n" ++
    s!"theorem {litNonnegOn} : NonnegOn {litName} {lo} {hi} := by\n" ++
    "  intro t hlo hhi\n" ++ theoremLadder cellPrefix "t" cells ++ "\n" ++
    s!"theorem {symNonnegOn} : NonnegOn {symName} {lo} {hi} := by\n" ++
    s!"  rw [{certEqName}]\n  exact {litNonnegOn}\n\n" ++
    s!"theorem {pointwiseName} {lb}t : Int{rb} (hlo : {lo} ≤ t) (hhi : t ≤ {hi}) :\n" ++
    s!"    0 ≤ evalPoly {symName} t :=\n  {symNonnegOn} t hlo hhi\n\nend {ns}\n"
where
  lb := "{"
  rb := "}"

def emitBernstein (literalModule coverModule cellModPrefix cellPrefix litName
    certEqName litNonnegOn symNonnegOn pointwiseName symName eqTac : String)
    (C : List Int) (lo hi : Int) : IO (List String × List Nat) := do
  match search C 1024 16 lo hi with
  | none => throw <| IO.userError s!"{coverModule} has no Bernstein cover"
  | some cells =>
      let specs := cells.map (·.spec)
      emitCells outDir s!"ExpProof.Cert.{literalModule}" "ExpCertV"
        cellModPrefix cellPrefix litName cells
      IO.FS.writeFile s!"{outDir}/{coverModule}.lean"
        (coverText s!"ExpProof.Cert.{literalModule}" cellModPrefix "ExpCertV"
          litName certEqName litNonnegOn symNonnegOn pointwiseName symName eqTac cellPrefix
          lo hi specs)
      let outputs := [s!"{coverModule}.lean"] ++
        cells.zipIdx.map fun (_, i) => s!"{cellModPrefix}{pad2 i}.lean"
      pure (outputs, cells.map (·.spec.bits))

def emitKronecker (literalModule coverModule cellModPrefix cellPrefix litName
    certEqName litNonnegOn symNonnegOn pointwiseName symName eqTac : String)
    (C : List Int) (lo hi : Int) : IO (List String × List Nat) := do
  match walkK C 1024 128 lo hi with
  | none => throw <| IO.userError s!"{coverModule} has no Kronecker cover"
  | some cells =>
      emitKCells outDir s!"ExpProof.Cert.{literalModule}" "ExpCertV"
        cellModPrefix cellPrefix litName cells
      IO.FS.writeFile s!"{outDir}/{coverModule}.lean"
        (coverText s!"ExpProof.Cert.{literalModule}" cellModPrefix "ExpCertV"
          litName certEqName litNonnegOn symNonnegOn pointwiseName symName eqTac cellPrefix
          lo hi cells)
      let outputs := [s!"{coverModule}.lean"] ++
        cells.zipIdx.map fun (_, i) => s!"{cellModPrefix}{pad2 i}.lean"
      pure (outputs, cells.map (·.bits))

def upEqTac : String :=
  "  have hy : yUB = yUBLit := by unfold yUB numExpV evNumVPoly todNumV odNumVPoly mulT2; decide +kernel\n" ++
  "  have hw : wUB = wUBLit := by unfold wUB denExpV evNumVPoly todNumV odNumVPoly mulT2; decide +kernel\n" ++
  "  have ht : tailUp = tailUpLit := by unfold tailUp expN27; decide +kernel\n" ++
  "  unfold certExpUp\n  rw [hy, hw, ht]\n  decide +kernel"

def loEqTac : String :=
  "  have he : expN27 = expN27Lit := by unfold expN27; decide +kernel\n" ++
  "  have hy : yLB = yLBLit := by unfold yLB numExpV evNumVPoly todNumV odNumVPoly mulT2; decide +kernel\n" ++
  "  have hw : wLB = wLBLit := by unfold wLB denExpV evNumVPoly todNumV odNumVPoly mulT2; decide +kernel\n" ++
  "  unfold certExpLo\n  rw [he, hy, hw]\n  decide +kernel"

def numEqTac : String :=
  "  unfold numExpV evNumVPoly todNumV odNumVPoly mulT2\n  decide +kernel"

def denEqTac : String :=
  "  unfold certDenM1 denExpV evNumVPoly todNumV odNumVPoly mulT2\n  decide +kernel"

def dOverEqTac : String :=
  "  unfold certDOver certDOverP evVPoly odVPoly\n  decide +kernel"

def dOverPEqTac : String :=
  "  unfold certDOverP evVPoly odVPoly\n  decide +kernel"

def dUnderPEqTac : String :=
  "  unfold certDUnderP evVPoly odVPoly\n  decide +kernel"

def generate : IO Unit := do
  let cUp := ptrim certExpUp
  let cLo := ptrim certExpLo
  IO.FS.writeFile s!"{outDir}/ExpVTaylorUpLit.lean" <| literalText <|
    litText "yUBLit" (ptrim yUB) ++ litText "wUBLit" (ptrim wUB) ++
    litText "tailUpLit" (ptrim tailUp) ++ litText "certExpUpLit" cUp
  IO.FS.writeFile s!"{outDir}/ExpVTaylorLoLit.lean" <| literalText <|
    litText "expN27Lit" (ptrim expN27) ++ litText "yLBLit" (ptrim yLB) ++
    litText "wLBLit" (ptrim wLB) ++ litText "certExpLoLit" cLo
  IO.FS.writeFile s!"{outDir}/ExpVNumLit.lean" <| literalText <|
    litText "numExpVLit" (ptrim numExpV)
  IO.FS.writeFile s!"{outDir}/ExpVDenLit.lean" <| literalText <|
    litText "certDenM1Lit" (ptrim certDenM1)
  IO.FS.writeFile s!"{outDir}/ExpVDOverLit.lean" <| literalText <|
    litText "certDOverLit" (ptrim certDOver)
  let mut overLits := ""
  let mut underLits := ""
  for (piece, i) in granPieces.zipIdx do
    let (_, _, T, dOver, dUnder) := piece
    overLits := overLits ++ litText s!"certDOvP{pad2 i}Lit" (ptrim (certDOverP T dOver))
    underLits := underLits ++ litText s!"certDUnP{pad2 i}Lit" (ptrim (certDUnderP T dUnder))
  IO.FS.writeFile s!"{outDir}/ExpVGranOverLit.lean" (literalText overLits)
  IO.FS.writeFile s!"{outDir}/ExpVGranUnderLit.lean" (literalText underLits)

  let mut expected := ["ExpVTaylorUpLit.lean", "ExpVTaylorLoLit.lean",
    "ExpVNumLit.lean", "ExpVDenLit.lean", "ExpVDOverLit.lean",
    "ExpVGranOverLit.lean", "ExpVGranUnderLit.lean"]

  let (upFiles, upBits) ← emitBernstein "ExpVTaylorUpLit" "ExpVUp" "ExpVUpC"
    "expVUp_cell" "certExpUpLit" "certExpUp_eq" "expVUpLit_nonnegOn"
    "expVUp_nonnegOn" "expVUp_nonneg" "certExpUp" upEqTac cUp 0 (H129 : Int)
  expected := expected ++ upFiles
  let (loFiles, loBits) ← emitBernstein "ExpVTaylorLoLit" "ExpVLo" "ExpVLoC"
    "expVLo_cell" "certExpLoLit" "certExpLo_eq" "expVLoLit_nonnegOn"
    "expVLo_nonnegOn" "expVLo_nonneg" "certExpLo" loEqTac cLo 0 (H129 : Int)
  expected := expected ++ loFiles
  let (numFiles, _) ← emitKronecker "ExpVNumLit" "ExpVNum" "ExpVNumC"
    "expVNum_cell" "numExpVLit" "numExpV_eq" "numExpVLit_nonnegOn"
    "numExpV_nonnegOn" "numExpV_nonneg" "numExpV" numEqTac (ptrim numExpV) 0 (H129 : Int)
  expected := expected ++ numFiles
  let (denFiles, _) ← emitKronecker "ExpVDenLit" "ExpVDenM1" "ExpVDenM1C"
    "expVDenM1_cell" "certDenM1Lit" "certDenM1_eq" "denM1VLit_nonnegOn"
    "denM1V_nonnegOn" "denM1V_nonneg" "certDenM1" denEqTac (ptrim certDenM1) 0 (H129 : Int)
  expected := expected ++ denFiles
  let (overFiles, _) ← emitKronecker "ExpVDOverLit" "ExpVDOver" "ExpVDOverC"
    "expVDOver_cell" "certDOverLit" "certDOver_eq" "dOverVLit_nonnegOn"
    "dOverV_nonnegOn" "dOverV_nonneg" "certDOver" dOverEqTac (ptrim certDOver)
    0 ((vmaxV : Int) + 1)
  expected := expected ++ overFiles

  for (piece, i) in granPieces.zipIdx do
    let (vlo, vhi, T, dOver, dUnder) := piece
    let suffix := pad2 i
    let (dOverFiles, _) ← emitKronecker "ExpVGranOverLit" s!"ExpVDOvP{suffix}"
      s!"ExpVDOvP{suffix}C" s!"dOvP{suffix}_cell" s!"certDOvP{suffix}Lit"
      s!"certDOvP{suffix}_eq" s!"dOvP{suffix}Lit_nonnegOn" s!"dOvP{suffix}_nonnegOn"
      s!"dOvP{suffix}_nonneg" s!"(certDOverP {T} {dOver})" dOverPEqTac
      (ptrim (certDOverP T dOver)) vlo (vhi + 1)
    expected := expected ++ dOverFiles
    let (dUnderFiles, _) ← emitKronecker "ExpVGranUnderLit" s!"ExpVDUnP{suffix}"
      s!"ExpVDUnP{suffix}C" s!"dUnP{suffix}_cell" s!"certDUnP{suffix}Lit"
      s!"certDUnP{suffix}_eq" s!"dUnP{suffix}Lit_nonnegOn" s!"dUnP{suffix}_nonnegOn"
      s!"dUnP{suffix}_nonneg" s!"(certDUnderP {T} {dUnder})" dUnderPEqTac
      (ptrim (certDUnderP T dUnder)) vlo (vhi + 1)
    expected := expected ++ dUnderFiles

  IO.FS.writeFile s!"{outDir}/ExpVTaylor.lean"
    "import ExpProof.Cert.ExpVUp\nimport ExpProof.Cert.ExpVLo\n"
  expected := expected ++ ["ExpVTaylor.lean"]
  reconcileOutputs outDir ["ExpV"] expected
  IO.println s!"Taylor upper: cells={upFiles.length - 1} B={upBits}"
  IO.println s!"Taylor lower: cells={loFiles.length - 1} B={loBits}"

end GenExpVLit

#eval GenExpVLit.generate

import ExpProof.Floor.UnderCarryDefs
import Common.GenCover

/-!
# Positive-under carry certificate generator

Each granularity row emits one literal polynomial and one independently
checked interval-Horner/Kronecker cell.  The façade transports those literal
certificates back to the symbolic carry polynomials.
-/

open Common.Poly Common.GenCover ExpCertV

namespace GenExpUnderCarry

def outDir : String := "ExpProof/Cert"

def literalModule (pieces : List (Int × Int × Int × Int)) : String :=
  let body := pieces.zipIdx.foldl (fun text row =>
    let ((_, _, T, R), i) := row
    text ++ litText s!"carryP{pad2 i}Lit" (carryCert T R))
    "namespace ExpCertV\n\n"
  body ++ "end ExpCertV\n"

def facadeModule (pieces : List (Int × Int × Int × Int)) : String :=
  let imports := pieces.zipIdx.foldl (fun text row =>
    let (_, i) := row
    text ++ s!"import ExpProof.Cert.ExpUnderCarryP{pad2 i}C00\n")
    "import ExpProof.Floor.UnderCarryDefs\nimport ExpProof.Cert.ExpUnderCarryLit\n"
  let theorems := pieces.zipIdx.foldl (fun text row =>
    let ((lo, hi, T, R), i) := row
    let suffix := pad2 i
    text ++ s!"theorem carryP{suffix}_eq : carryCert {T} {R} = carryP{suffix}Lit := by\n" ++
      "  unfold carryCert carryLhs denAtCap S2\n  decide +kernel\n\n" ++
      s!"theorem carryP{suffix}_nonnegOn :\n" ++
      s!"    NonnegOn (carryCert {T} {R}) {lo} {hi} := by\n" ++
      s!"  rw [carryP{suffix}_eq]\n" ++
      s!"  exact underCarryP{suffix}_cell00_nonnegOn\n\n" ++
      s!"theorem carryP{suffix}_nonneg {lb}v : Int{rb} (hlo : {lo} ≤ v) (hhi : v ≤ {hi}) :\n" ++
      s!"    0 ≤ evalPoly (carryCert {T} {R}) v :=\n" ++
      s!"  carryP{suffix}_nonnegOn v hlo hhi\n\n") ""
  imports ++
    "\nnamespace ExpCertV\n\nopen Common.Poly\n\n" ++
    "set_option maxRecDepth 100000\n\n" ++ theorems ++ "end ExpCertV\n"
where
  lb := "{"
  rb := "}"

def expectedOutputs (pieces : List (Int × Int × Int × Int)) : List String :=
  ["ExpUnderCarryLit.lean", "ExpUnderCarry.lean"] ++
    pieces.zipIdx.map fun (_, i) => s!"ExpUnderCarryP{pad2 i}C00.lean"

def generate : IO Unit := do
  if granPieces.length != underCarryBounds.length then
    throw <| IO.userError
      s!"carry table length mismatch: {granPieces.length} pieces, {underCarryBounds.length} bounds"
  if underCarryPieces.length != 32 then
    throw <| IO.userError s!"expected 32 carry pieces, got {underCarryPieces.length}"
  let mut accepted : List (Nat × Nat) := []
  for (piece, i) in underCarryPieces.zipIdx do
    let (lo, hi, T, R) := piece
    let C := carryCert T R
    let modPrefix := s!"ExpUnderCarryP{pad2 i}C"
    match walkK C 1024 1 lo hi with
    | some [cell] =>
        emitKCells outDir "ExpProof.Cert.ExpUnderCarryLit" "ExpCertV"
          modPrefix s!"underCarryP{pad2 i}_cell" s!"carryP{pad2 i}Lit" [cell]
        accepted := accepted ++ [(i, cell.bits)]
    | some cells =>
        throw <| IO.userError s!"piece {i} requires {cells.length} cells"
    | none =>
        throw <| IO.userError s!"piece {i} has no accepted one-cell certificate"
  reconcileOutputs outDir ["ExpUnderCarry"] (expectedOutputs underCarryPieces)
  IO.FS.writeFile s!"{outDir}/ExpUnderCarryLit.lean" (literalModule underCarryPieces)
  IO.FS.writeFile s!"{outDir}/ExpUnderCarry.lean" (facadeModule underCarryPieces)
  for (i, B) in accepted do
    IO.println s!"carry piece {pad2 i}: cells=1 B={B}"

end GenExpUnderCarry

#eval GenExpUnderCarry.generate

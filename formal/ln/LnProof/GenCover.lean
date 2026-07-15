import LnProof.Cert.FloorCertGeLoLit
import LnProof.Cert.FloorCertLtLoLit
import Common.Foundation.KroneckerShift
import Common.GenCover

/-!
# Cover generator

Greedily walks `[lo, hi]` for a certificate polynomial, computing at each anchor
`a` the largest cell width `w` with `0 ≤ (hornerIv (kShiftWitness kB C a) 0 w).1`
— exactly the predicate the in-kernel `checkCoverK` decides, so the emitted
covers are guaranteed `decide`-acceptable. Writes one `…C<NN>.lean` cell file
per sub-cell and one aggregate module containing the complete literal
`NonnegOn` proof.

Run with `lake env lean GenCover.lean` after building the two
`LnProof.Cert.FloorCert*Lit` modules and `Common.GenCover`.
-/

open Common.Poly LnFloorCert Common.GenCover

namespace GenCover

/-- Render the aggregate that imports every cell and joins their intervals. -/
def aggregateText (litName modPrefix cellPrefix nonnegName : String)
    (cells : List (Int × Int)) (lo hi : Int) : String :=
  let imports := String.join <| cells.zipIdx.map fun (_, i) =>
    s!"import LnProof.Cert.{modPrefix}{pad2 i}\n"
  let header :=
    "\nnamespace LnFloorCert\nopen Common.Poly\n\nset_option maxRecDepth 100000\n\n" ++
      s!"theorem {nonnegName} : NonnegOn {litName} {lo} {hi} := by\n" ++
      "  intro m h1 h2\n"
  let n := cells.length
  let ladder := String.join <| cells.zipIdx.map fun ((a, w), i) =>
    ladderStep s!"{cellPrefix}{pad2 i}" "m" a w (i + 1 == n)
  imports ++ header ++ ladder ++ "\nend LnFloorCert\n"

/-- Emit the complete declared output set for one cover. -/
def emit (nm litModule litName modPrefix cellPrefix aggregateModule nonnegName : String)
    (C : List Int) (lo hi : Int) : IO Unit := do
  let (ok, cells) := walk C lo hi
  if ! ok then
    throw <| IO.userError s!"{nm}: cover did not reach {hi}; tail={cells.drop (cells.length - 2)}"
  let cellOutputs := cells.zipIdx.map fun (_, i) => s!"{modPrefix}{pad2 i}.lean"
  let aggregateOutput := s!"{aggregateModule}.lean"
  let expected := cellOutputs ++ [aggregateOutput]
  reconcileOutputs "LnProof/Cert" [modPrefix, aggregateModule] expected
  for (aw, i) in cells.zipIdx do
    let (a, w) := aw
    let nn := pad2 i
    IO.FS.writeFile s!"LnProof/Cert/{modPrefix}{nn}.lean"
      (cellText s!"LnProof.Cert.{litModule}" "LnFloorCert" s!"{cellPrefix}{nn}" litName a w)
  IO.FS.writeFile s!"LnProof/Cert/{aggregateOutput}"
    (aggregateText litName modPrefix cellPrefix nonnegName cells lo hi)
  IO.println s!"{nm}: wrote {cells.length} cells and {aggregateOutput}"

end GenCover

open GenCover

def loLT : Int := 39614081257132168796771975168          -- 2^95
def hiLT : Int := 56022770974786139918731938181          -- Sc - 46
def loGE : Int := 56022770974786139918731938273          -- Sc + 46
def hiGE : Int := 79228162514264337593543950335          -- 2^96 - 1

#eval emit "certGeLo" "FloorCertGeLoLit" "certGeLoLit" "FloorCertGeLoC"
  "geLo_cell" "FloorCertGeLoCover" "certGeLoLit_nonnegOn" certGeLoLit loGE hiGE
#eval emit "certLtLo" "FloorCertLtLoLit" "certLtLoLit" "FloorCertLtLoC"
  "ltLo_cell" "FloorCertLtLoCover" "certLtLoLit_nonnegOn" certLtLoLit loLT hiLT

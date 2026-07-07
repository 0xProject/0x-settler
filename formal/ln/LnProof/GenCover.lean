import LnProof.Cert.FloorCertLit
import Common.Foundation.KroneckerShift
import Common.GenCover

/-!
# Cover generator

Greedily walks `[lo, hi]` for a certificate polynomial, computing at each anchor
`a` the largest cell width `w` with `0 ≤ (hornerIv (kShiftWitness kB C a) 0 w).1`
— exactly the predicate the in-kernel `checkCoverK` decides, so the emitted
covers are guaranteed `decide`-acceptable.  Writes one `…C<NN>.lean` cell file
per sub-cell and prints the `_nonneg` ladder and import block for the cover
module.

Run with `lake env lean GenCover.lean` (after `lake build LnProof.Cert.FloorCertLit Common.GenCover`).
-/

open Common.Poly LnFloorCert Common.GenCover

namespace GenCover

/-- Emit cell files `<modPrefix><NN>.lean` and return the ladder text. -/
def emit (nm litName symName evalEqName modPrefix cellPrefix nonnegName : String)
    (C : List Int) (lo hi : Int) : IO Unit := do
  let (ok, cells) := walk C lo hi
  IO.println s!"-- {nm}: reached={ok} ncells={cells.length}"
  if ! ok then
    IO.println s!"-- FAILED tail: {cells.drop (cells.length - 2)}"
    return
  -- write one cell file per sub-cell
  for (aw, i) in cells.zipIdx do
    let (a, w) := aw
    let nn := pad2 i
    IO.FS.writeFile s!"LnProof/Cert/{modPrefix}{nn}.lean"
      (cellText "LnProof.Cert.FloorCertLit" "LnFloorCert" s!"{cellPrefix}{nn}" litName a w)
  -- ladder + imports
  let mut imps := ""
  for (_, i) in cells.zipIdx do
    imps := imps ++ s!"import LnProof.Cert.{modPrefix}{pad2 i}\n"
  IO.println "==== IMPORTS ===="
  IO.println imps
  IO.println "==== LADDER ===="
  let lb := "{"
  let rb := "}"
  IO.println s!"theorem {nonnegName} {lb}m : Int{rb} (h1 : {lo} ≤ m) (h2 : m ≤ {hi}) :"
  IO.println s!"    0 ≤ evalPoly {symName} m := by"
  IO.println s!"  have hev := {evalEqName} m"
  IO.println "  rw [hev]"
  let n := cells.length
  for (aw, i) in cells.zipIdx do
    let (a, w) := aw
    IO.print (ladderStep s!"{cellPrefix}{pad2 i}" "m" a w (i + 1 == n))

end GenCover

open GenCover

def loLT : Int := 39614081257132168796771975168          -- 2^95
def hiLT : Int := 56022770974786139918731938181          -- Sc - 46
def loGE : Int := 56022770974786139918731938273          -- Sc + 46
def hiGE : Int := 79228162514264337593543950335          -- 2^96 - 1

-- Generate the floor cert covers: never-overshoot upper forms (GeUp/LtUp) and
-- not-too-low lower forms (GeLo/LtLo). The cover modules keep their hand-written
-- eval_eq; only the cell files and the _nonneg ladder are generated.
#eval emit "certGeUp" "certGeUpLit" "certGeUp" "geUp_eval_eq" "FloorCertGeUpC" "geUp_cell" "geUp_nonneg" certGeUpLit loGE hiGE
#eval emit "certLtUp" "certLtUpLit" "certLtUp" "ltUp_eval_eq" "FloorCertLtUpC" "ltUp_cell" "ltUp_nonneg" certLtUpLit loLT hiLT
#eval emit "certGeLo" "certGeLoLit" "certGeLo" "geLo_eval_eq" "FloorCertGeLoC" "geLo_cell" "geLo_nonneg" certGeLoLit loGE hiGE
#eval emit "certLtLo" "certLtLoLit" "certLtLo" "ltLo_eval_eq" "FloorCertLtLoC" "ltLo_cell" "ltLo_nonneg" certLtLoLit loLT hiLT

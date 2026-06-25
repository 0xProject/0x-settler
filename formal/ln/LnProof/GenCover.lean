import LnProof.FloorCertLit
import LnProof.KroneckerShift

/-!
# Cover generator (committed tool)

Greedily walks `[lo, hi]` for a certificate polynomial, computing at each anchor
`a` the largest cell width `w` with `0 ≤ (hornerIv (kShiftWitness kB C a) 0 w).1`
— exactly the predicate the in-kernel `checkCoverK` decides, so the emitted
covers are guaranteed `decide`-acceptable.  Writes one `…C<NN>.lean` cell file
per sub-cell and prints the `_nonneg` ladder + import block to splice into the
cover module.

Run with `lake env lean GenCover.lean` (after `lake build LnProof.FloorCertLit`).
-/

open LnPoly LnFloorCert

namespace GenCover

/-- Largest `w ∈ [0, hiW]` with `0 ≤ (hornerIv S 0 w).1` (non-increasing in `w`). -/
partial def maxW (S : List Int) (hiW : Int) : Int :=
  let rec bs (lo hi : Int) : Int :=
    if lo ≥ hi then lo
    else
      let mid := (lo + hi + 1) / 2
      if 0 ≤ (hornerIv S 0 mid).1 then bs mid hi else bs lo (mid - 1)
  bs 0 hiW

/-- Greedy walk → `(reached?, (anchor, width) list)`. -/
partial def walk (C : List Int) (lo hi : Int) : Bool × List (Int × Int) :=
  let rec go (a : Int) (fuel : Nat) (acc : List (Int × Int)) : Bool × List (Int × Int) :=
    match fuel with
    | 0 => (false, acc.reverse)
    | fuel + 1 =>
      if a > hi then (true, acc.reverse)
      else
        let S := kShiftWitness kB C a
        if 0 ≤ (hornerIv S 0 0).1 then
          let w := maxW S (hi - a)
          go (a + w + 1) fuel ((a, w) :: acc)
        else (false, ((a, -1) :: acc).reverse)
  go lo 200000 []

def pad2 (i : Nat) : String := (if i < 10 then "0" else "") ++ toString i

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
    let body :=
      s!"import LnProof.FloorCertLit\nimport LnProof.KroneckerShift\n\nnamespace LnFloorCert\nopen LnPoly\n\nset_option maxRecDepth 100000\n\ntheorem {cellPrefix}{nn} : checkCoverK kB {litName} {a} {a + w}\n    [{w}] = true := by\n  decide +kernel\n\nend LnFloorCert\n"
    IO.FS.writeFile s!"LnProof/{modPrefix}{nn}.lean" body
  -- ladder + imports
  let mut imps := ""
  for (_, i) in cells.zipIdx do
    imps := imps ++ s!"import LnProof.{modPrefix}{pad2 i}\n"
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
    if i + 1 < n then
      IO.println s!"  rcases Int.lt_or_le m ({a + w} + 1) with h | h"
      IO.println s!"  · exact checkCoverK_sound _ _ _ _ _ {cellPrefix}{pad2 i} m (by omega) (by omega)"
    else
      IO.println s!"  exact checkCoverK_sound _ _ _ _ _ {cellPrefix}{pad2 i} m (by omega) h2"

end GenCover

open GenCover

def loLT : Int := 39614081257132168796771975168          -- 2^95
def hiLT : Int := 56022770974786139918731938181          -- Sc - 46
def loGE : Int := 56022770974786139918731938273          -- Sc + 46
def hiGE : Int := 79228162514264337593543950335          -- 2^96 - 1

-- Regenerate the never-overshoot covers (the +form certs at EUN=3382).
#eval emit "certGeUp" "certGeUpLit" "certGeUp" "geUp_eval_eq" "FloorCertGeUpC" "geUp_cell" "geUp_nonneg" certGeUpLit loGE hiGE
#eval emit "certLtUp" "certLtUpLit" "certLtUp" "ltUp_eval_eq" "FloorCertLtUpC" "ltUp_cell" "ltUp_nonneg" certLtUpLit loLT hiLT

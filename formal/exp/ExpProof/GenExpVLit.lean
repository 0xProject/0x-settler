import ExpProof.Floor.CertDefsV
import Common.Foundation.KroneckerShift

/-!
# Cert literal + cover generator for the **v-form** reduced-argument Taylor caps

Computes the never-over (`certExpUp`) and not-two-below (`certExpLo`) v-form certificate polynomials
from the symbolic `ExpCertV` definitions, emits the building-block + cert literal coefficient lists
(`Cert/ExpVCertLit.lean`), then greedily walks `[0, H128]` for each — exactly the predicate the
in-kernel `checkCoverK` decides — and writes one `Cert/ExpV{Up,Lo,…}C<NN>.lean` cell file per sub-cell
plus the cover module with the symbolic-cert↔literal equality and the `_nonneg` ladder.

Run with `lake env lean GenExpVLit.lean` after `lake build ExpProof.Floor.CertDefsV`. Output is
deterministic (byte-identical on re-run). Only the generated `Cert/ExpV*` files are machine output;
this generator and the hand-written `Floor/CertDefsV.lean` symbolic definitions are tracked.
-/

open Common.Poly ExpCertV

namespace GenExpVLit

/-- Drop trailing zero coefficients. -/
def ptrim (a : List Int) : List Int :=
  let r := (a.reverse.dropWhile (· == 0)).reverse
  if r.isEmpty then [0] else r

/-- Largest `w ∈ [0, hiW]` with `0 ≤ (hornerIv S 0 w).1` (non-increasing in `w`). -/
partial def maxW (S : List Int) (hiW : Int) : Int :=
  let rec bs (lo hi : Int) : Int :=
    if lo ≥ hi then lo
    else let mid := (lo + hi + 1) / 2
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

/-- Walk `[lo, hi]`, write one cell file per sub-cell, then write the cover module. -/
def emit (litName coverMod modPrefix cellPrefix certEqName litNonneg symNonneg symName eqTac : String)
    (C : List Int) (lo hi : Int) : IO Unit := do
  let (ok, cells) := walk C lo hi
  IO.println s!"-- {coverMod}: reached={ok} ncells={cells.length}"
  if ! ok then IO.println s!"-- FAILED tail: {cells.drop (cells.length - 2)}"; return
  for (aw, i) in cells.zipIdx do
    let (a, w) := aw
    IO.FS.writeFile s!"ExpProof/Cert/{modPrefix}{pad2 i}.lean"
      s!"import ExpProof.Cert.ExpVCertLit\nimport Common.Foundation.KroneckerShift\n\nnamespace ExpCertV\nopen Common.Poly\n\nset_option maxRecDepth 100000\n\ntheorem {cellPrefix}{pad2 i} : checkCoverK kB {litName} {a} {a + w}\n    [{w}] = true := by\n  decide +kernel\n\nend ExpCertV\n"
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
    if i + 1 < n then
      s := s ++ s!"  rcases Int.lt_or_le t ({a + w} + 1) with h | h\n  · exact checkCoverK_sound _ _ _ _ _ {cellPrefix}{pad2 i} t (by omega) (by omega)\n"
    else
      s := s ++ s!"  exact checkCoverK_sound _ _ _ _ _ {cellPrefix}{pad2 i} t (by omega) h2\n"
  s := s ++ s!"\ntheorem {symNonneg} {lb}t : Int{rb} (h1 : {lo} ≤ t) (h2 : t ≤ {hi}) :\n"
  s := s ++ s!"    0 ≤ evalPoly {symName} t := by\n  rw [{certEqName}]; exact {litNonneg} h1 h2\n"
  s := s ++ "\nend ExpCertV\n"
  IO.FS.writeFile s!"ExpProof/Cert/{coverMod}.lean" s

def litText (name : String) (c : List Int) : String :=
  "def " ++ name ++ " : List Int := [\n  " ++
    String.intercalate ",\n  " (c.map toString) ++ "]\n\n"

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

#eval do
  let cUp := ptrim certExpUp
  let cLo := ptrim certExpLo
  IO.FS.writeFile "ExpProof/Cert/ExpVCertLit.lean"
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
      "end ExpCertV\n")
  IO.println "v-form literals written"
  emit "certExpUpLit" "ExpVUp" "ExpVUpC" "expVUp_cell" "certExpUp_eq" "expVUpLit_nonneg"
    "expVUp_nonneg" "certExpUp" upEqTac cUp 0 (H128 : Int)
  emit "certExpLoLit" "ExpVLo" "ExpVLoC" "expVLo_cell" "certExpLo_eq" "expVLoLit_nonneg"
    "expVLo_nonneg" "certExpLo" loEqTac cLo 0 (H128 : Int)
  emit "numExpVLit" "ExpVNum" "ExpVNumC" "expVNum_cell" "numExpV_eq" "numExpVLit_nonneg"
    "numExpV_nonneg" "numExpV" numEqTac (ptrim numExpV) 0 (H128 : Int)
  emit "certDenM1Lit" "ExpVDenM1" "ExpVDenM1C" "expVDenM1_cell" "certDenM1_eq" "denM1VLit_nonneg"
    "denM1V_nonneg" "certDenM1" denM1EqTac (ptrim certDenM1) 0 (H128 : Int)

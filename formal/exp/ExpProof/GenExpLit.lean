import ExpProof.Floor.CertDefs
import Common.Foundation.KroneckerShift

/-!
# Cert literal + cover generator for the reduced-argument Taylor caps

Computes the never-over (`certExpUp`) and not-two-below (`certExpLo`) certificate polynomials from
the symbolic `ExpCert` definitions, emits all the building-block + cert literal coefficient lists
(`Cert/ExpCertLit.lean`), then greedily walks `[0, H128]` for each — at every anchor `a` taking the
largest cell width `w` with `0 ≤ (hornerIv (kShiftWitness kB C a) 0 w).1`, exactly the predicate the
in-kernel `checkCoverK` decides — and writes one `Cert/Exp{Up,Lo}C<NN>.lean` cell file per sub-cell
plus the cover module (`Cert/ExpUp.lean`/`Cert/ExpLo.lean`) with the symbolic-cert↔literal equality
and the `_nonneg` ladder.

Run with `lake env lean GenExpLit.lean` after `lake build ExpProof.Floor.CertDefs`. Output is
deterministic (byte-identical on re-run). Only the generated `Cert/*` files are machine output; this
generator and the hand-written `Floor/CertDefs.lean` symbolic definitions are tracked.
-/

open Common.Poly ExpCert

namespace GenExpLit

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

/-- Walk `[lo, hi]`, write one cell file per sub-cell, then write the cover module: the cell
imports, the symbolic-cert↔literal equality `{certEqName}` (built by rewriting the building-block
literals so the kernel never has to whnf the full symbolic construction), the `{litNonneg}` cell
ladder over the literal, and `{symNonneg}` lifting it to the symbolic cert. `eqTac` rewrites the
symbolic cert to its literal via the block equalities. -/
def emit (litName coverMod modPrefix cellPrefix certEqName litNonneg symNonneg symName eqTac : String)
    (C : List Int) (lo hi : Int) : IO Unit := do
  let (ok, cells) := walk C lo hi
  IO.println s!"-- {coverMod}: reached={ok} ncells={cells.length}"
  if ! ok then IO.println s!"-- FAILED tail: {cells.drop (cells.length - 2)}"; return
  for (aw, i) in cells.zipIdx do
    let (a, w) := aw
    IO.FS.writeFile s!"ExpProof/Cert/{modPrefix}{pad2 i}.lean"
      s!"import ExpProof.Cert.ExpCertLit\nimport Common.Foundation.KroneckerShift\n\nnamespace ExpCert\nopen Common.Poly\n\nset_option maxRecDepth 100000\n\ntheorem {cellPrefix}{pad2 i} : checkCoverK kB {litName} {a} {a + w}\n    [{w}] = true := by\n  decide +kernel\n\nend ExpCert\n"
  let lb := "{"; let rb := "}"
  let mut s := "import ExpProof.Floor.CertDefs\nimport ExpProof.Cert.ExpCertLit\nimport Common.Foundation.KroneckerShift\n"
  for (_, i) in cells.zipIdx do s := s ++ s!"import ExpProof.Cert.{modPrefix}{pad2 i}\n"
  s := s ++ s!"\nnamespace ExpCert\nopen Common.Poly\n\nset_option maxRecDepth 100000\n\n"
  -- the symbolic cert equals the emitted literal: rewrite the building blocks to their
  -- literals (each shallow enough for the kernel), then the residual `polyMul`/`polySub`/
  -- `polyScale` is over literal lists and reduces by `decide +kernel`.
  s := s ++ s!"theorem {certEqName} : {symName} = {litName} := by\n{eqTac}\n\n"
  -- the cell ladder over the literal
  s := s ++ s!"theorem {litNonneg} {lb}t : Int{rb} (h1 : {lo} ≤ t) (h2 : t ≤ {hi}) :\n"
  s := s ++ s!"    0 ≤ evalPoly {litName} t := by\n"
  let n := cells.length
  for (aw, i) in cells.zipIdx do
    let (a, w) := aw
    if i + 1 < n then
      s := s ++ s!"  rcases Int.lt_or_le t ({a + w} + 1) with h | h\n  · exact checkCoverK_sound _ _ _ _ _ {cellPrefix}{pad2 i} t (by omega) (by omega)\n"
    else
      s := s ++ s!"  exact checkCoverK_sound _ _ _ _ _ {cellPrefix}{pad2 i} t (by omega) h2\n"
  -- lift to the symbolic cert
  s := s ++ s!"\ntheorem {symNonneg} {lb}t : Int{rb} (h1 : {lo} ≤ t) (h2 : t ≤ {hi}) :\n"
  s := s ++ s!"    0 ≤ evalPoly {symName} t := by\n  rw [{certEqName}]; exact {litNonneg} h1 h2\n"
  s := s ++ "\nend ExpCert\n"
  IO.FS.writeFile s!"ExpProof/Cert/{coverMod}.lean" s

def litText (name : String) (c : List Int) : String :=
  "def " ++ name ++ " : List Int := [\n  " ++
    String.intercalate ",\n  " (c.map toString) ++ "]\n\n"

end GenExpLit

open GenExpLit

/-- Tactic block proving `certExpUp = certExpUpLit`. -/
def upEqTac : String :=
  "  have hy : yUB = yUBLit := by unfold yUB numExp evNum todNum odNum mulT2; decide +kernel\n" ++
  "  have hw : wUB = wUBLit := by unfold wUB denExp evNum todNum odNum mulT2; decide +kernel\n" ++
  "  have ht : tailUp = tailUpLit := by unfold tailUp expN27; decide +kernel\n" ++
  "  unfold certExpUp\n  rw [hy, hw, ht]\n  decide +kernel"

/-- Tactic block proving `certExpLo = certExpLoLit`. -/
def loEqTac : String :=
  "  have he : expN27 = expN27Lit := by unfold expN27; decide +kernel\n" ++
  "  have hy : yLB = yLBLit := by unfold yLB numExp evNum todNum odNum mulT2; decide +kernel\n" ++
  "  have hw : wLB = wLBLit := by unfold wLB denExp evNum todNum odNum mulT2; decide +kernel\n" ++
  "  unfold certExpLo\n  rw [he, hy, hw]\n  decide +kernel"

/-- Tactic block proving `numExp = numExpLit`. -/
def numEqTac : String :=
  "  unfold numExp evNum todNum odNum mulT2\n  decide +kernel"

/-- Tactic block proving `certDenM1 = certDenM1Lit`. -/
def denM1EqTac : String :=
  "  unfold certDenM1 denExp evNum todNum odNum mulT2\n  decide +kernel"

#eval do
  let cUp := ptrim certExpUp
  let cLo := ptrim certExpLo
  -- the building-block literals (degree ≤ 27) the cert-equality proofs rewrite through, plus
  -- the cert/denominator literals the cells reference.
  IO.FS.writeFile "ExpProof/Cert/ExpCertLit.lean"
    ("/-! Generated cut-certificate literal coefficient lists. -/\n\nnamespace ExpCert\n\n" ++
      litText "numExpLit" (ptrim numExp) ++
      litText "denExpLit" (ptrim denExp) ++
      litText "expN27Lit" (ptrim expN27) ++
      litText "tailUpLit" (ptrim tailUp) ++
      litText "yUBLit" (ptrim yUB) ++
      litText "wUBLit" (ptrim wUB) ++
      litText "yLBLit" (ptrim yLB) ++
      litText "wLBLit" (ptrim wLB) ++
      litText "certDenM1Lit" (ptrim certDenM1) ++
      litText "certExpUpLit" cUp ++
      litText "certExpLoLit" cLo ++
      "end ExpCert\n")
  IO.println "literals written"
  emit "certExpUpLit" "ExpUp" "ExpUpC" "expUp_cell" "certExpUp_eq" "expUpLit_nonneg"
    "expUp_nonneg" "certExpUp" upEqTac cUp 0 (H128 : Int)
  emit "certExpLoLit" "ExpLo" "ExpLoC" "expLo_cell" "certExpLo_eq" "expLoLit_nonneg"
    "expLo_nonneg" "certExpLo" loEqTac cLo 0 (H128 : Int)
  emit "numExpLit" "ExpNum" "ExpNumC" "expNum_cell" "numExp_eq" "numExpLit_nonneg"
    "numExp_nonneg" "numExp" numEqTac (ptrim numExp) 0 (H128 : Int)
  emit "certDenM1Lit" "ExpDenM1" "ExpDenM1C" "denM1_cell" "certDenM1_eq" "denM1Lit_nonneg"
    "denM1_nonneg" "certDenM1" denM1EqTac (ptrim certDenM1) 0 (H128 : Int)

import LnProof.Cert.FloorCertLtLoLit
import LnProof.Error.Core.Budget
import Common.Foundation.KroneckerShift
import Common.GenCover

/-! Generate the error-bound certificate literal `ErrCertLtLit` and its cover
for the current `BIASc` and `lnErrorBoundNum`. Computes `certErrLt` inline so
generation does not depend on the bridge building, then walks the `checkCoverK`
cover used by `errLt_nonnegOn`. -/

open Common.Poly LnFloorCert Common.Exp LnFloor LnYul
open Common.GenCover hiding litText

namespace GenErrLit

def biasCapNum : Nat :=
  (Common.Exp.expNum 130 (BIASc * 2 ^ 27) QS * (10 ^ 18 * 10 ^ 42)) / (Common.Exp.fact 130 * QS ^ 130)
def errLtK : Int := (10 ^ 31 * (10 ^ 18 * 10 ^ 42) * lnErrQ * (10 ^ 40 + 160) : Nat)
def errLtW : Nat := biasCapNum * (lnErrQ + minPosAvail) * wadRayStrictDen * 10 ^ 40

def cLt : List Int :=
  polyAdd (polyScale ((errLtW : Int) * (fact 23 : Int)) (polyPow ltTDLit 23))
    (polyScale (-errLtK) (polyMul [1, 1]
      (polyAdd (polyScale 23 (polyMul (expPolyNum ltTNLit ltTDLit 22) ltTDLit))
        (polyScale 2 (polyPow ltTNLit 23)))))

/-- A literal block wrapped in the namespace consumed by the cover. -/
def litText (name : String) (c : List Int) : String :=
  "namespace LnFloorCert\n\n" ++ Common.GenCover.litText name c ++ "end LnFloorCert\n"

/-- Emit the literal, cells, and aggregate for the complete cover. -/
def emit (litFile litName coverMod modPrefix cellPrefix nonnegName : String) (C : List Int) (lo hi : Int) : IO Unit := do
  let (ok, cells) := walk C lo hi
  IO.println s!"-- {coverMod}: reached={ok} ncells={cells.length}"
  if ! ok then
    throw <| IO.userError s!"{coverMod}: cover did not reach {hi}; tail={cells.drop (cells.length - 2)}"
  let cellOutputs := cells.zipIdx.map fun (_, i) => s!"{modPrefix}{pad2 i}.lean"
  let litOutput := s!"{litFile}.lean"
  let coverOutput := s!"{coverMod}.lean"
  let expected := cellOutputs ++ [litOutput, coverOutput]
  reconcileOutputs "LnProof/Cert" [modPrefix, litFile, coverMod] expected
  IO.FS.writeFile s!"LnProof/Cert/{litOutput}" (litText litName (ptrim C))
  for (aw, i) in cells.zipIdx do
    let (a, w) := aw
    IO.FS.writeFile s!"LnProof/Cert/{modPrefix}{pad2 i}.lean"
      (cellText s!"LnProof.Cert.{litFile}" "LnFloorCert" s!"{cellPrefix}{pad2 i}" litName a w)
  let mut s := ""
  for (_, i) in cells.zipIdx do s := s ++ s!"import LnProof.Cert.{modPrefix}{pad2 i}\n"
  s := s ++ s!"\nnamespace LnFloorCert\nopen Common.Poly\n\nset_option maxRecDepth 100000\n\n"
  s := s ++ s!"theorem {nonnegName}On : NonnegOn {litName} {lo} {hi} := by\n  intro m h1 h2\n"
  let n := cells.length
  for (aw, i) in cells.zipIdx do
    let (a, w) := aw
    s := s ++ ladderStep s!"{cellPrefix}{pad2 i}" "m" a w (i + 1 == n)
  s := s ++ "\nend LnFloorCert\n"
  IO.FS.writeFile s!"LnProof/Cert/{coverOutput}" s

end GenErrLit
open GenErrLit
def loLT : Int := 39614081257132168796771975168
def hiLT : Int := 56022770974786139918731938181

#eval do
  emit "ErrCertLtLit" "certErrLtLit" "ErrCertLt" "ErrCertLtC" "errLt_cell" "errLt_nonneg" (ptrim cLt) loLT hiLT

import LnProof.Cert.FloorCertGeLoLit
import LnProof.Cert.FloorCertLtLoLit
import LnProof.Error.Core.ExpMargin
import LnProof.Error.Core.Budget
import Common.Foundation.KroneckerShift
import Common.GenCover

/-! Generate the error-bound cert literals (ErrCertLtLit / ErrCertGeLit) and
their covers for the current BIASc and `lnErrorBoundNum`. Computes
`certErrLt`/`certErrGe`
inline (mirroring the ErrCert*Bridge constructions) so it does not depend on the
bridges building, then walks the `checkCoverK` covers (literal signature, as the
checked `errLt_nonnegOn`/`errGe_nonnegOn` theorems use). -/

open Common.Poly LnFloorCert Common.Exp LnFloor LnYul
open Common.GenCover hiding litText

namespace GenErrLit

-- All derived from the model inputs (BIASc in the model and `lnErrorBoundNum`
-- in ErrorBoundCert), so generation tracks changes to those.
def biasCapNum : Nat :=
  (Common.Exp.expNum 130 (BIASc * 2 ^ 27) QS * (10 ^ 18 * 10 ^ 42)) / (Common.Exp.fact 130 * QS ^ 130)
def errLtK : Int := (10 ^ 31 * (10 ^ 18 * 10 ^ 42) * lnErrQ * (10 ^ 40 + 160) : Nat)
def errGeK : Int := errLtK
def errLtW : Nat := biasCapNum * (lnErrQ + minPosAvail) * wadRayStrictDen * 10 ^ 40
def errGeW : Nat := biasCapNum * (lnErrQ + (692115493 * 2 ^ 99 + 2 ^ 27 * 10 ^ 9)) * wadRayStrictDen * 10 ^ 40

def cLt : List Int :=
  polyAdd (polyScale ((errLtW : Int) * (fact 23 : Int)) (polyPow ltTDLit 23))
    (polyScale (-errLtK) (polyMul [1, 1]
      (polyAdd (polyScale 23 (polyMul (expPolyNum ltTNLit ltTDLit 22) ltTDLit))
        (polyScale 2 (polyPow ltTNLit 23)))))

def cGe : List Int :=
  expMarginPoly 22 geTN2bLit geTD2bLit (polyScale errGeK [1, 1]) errGeW

/-- Walk `[lo,hi]`, write one cell file per sub-cell, and write the complete
cover module `coverMod` (cell imports + the literal-signature `nonnegName`
ladder). The error covers carry no hand-written content, so they are fully
generated. -/
def emit (litFile litName coverMod modPrefix cellPrefix nonnegName : String) (C : List Int) (lo hi : Int) : IO Unit := do
  let (ok, cells) := walk C lo hi
  IO.println s!"-- {coverMod}: reached={ok} ncells={cells.length}"
  if ! ok then IO.println s!"-- FAILED tail: {cells.drop (cells.length-2)}"; return
  let expected := cells.zipIdx.map fun (_, i) => s!"{modPrefix}{pad2 i}.lean"
  reconcileOutputs "LnProof/Cert" [modPrefix] expected
  for (aw, i) in cells.zipIdx do
    let (a, w) := aw
    IO.FS.writeFile s!"LnProof/Cert/{modPrefix}{pad2 i}.lean"
      (cellText s!"LnProof.Cert.{litFile}" "LnFloorCert" s!"{cellPrefix}{pad2 i}" litName a w)
  let lb := "{"; let rb := "}"
  let mut s := ""
  for (_, i) in cells.zipIdx do s := s ++ s!"import LnProof.Cert.{modPrefix}{pad2 i}\n"
  s := s ++ s!"\nnamespace LnFloorCert\nopen Common.Poly\n\nset_option maxRecDepth 100000\n\n"
  s := s ++ s!"theorem {nonnegName}On : NonnegOn {litName} {lo} {hi} := by\n  intro m h1 h2\n"
  let n := cells.length
  for (aw, i) in cells.zipIdx do
    let (a, w) := aw
    s := s ++ ladderStep s!"{cellPrefix}{pad2 i}" "m" a w (i + 1 == n)
  s := s ++ s!"\ntheorem {nonnegName} {lb}m : Int{rb} (h1 : {lo} ≤ m) (h2 : m ≤ {hi}) :\n    0 ≤ evalPoly {litName} m :=\n  {nonnegName}On m h1 h2\n"
  s := s ++ "\nend LnFloorCert\n"
  IO.FS.writeFile s!"LnProof/Cert/{coverMod}.lean" s

/-- A shared-emitter literal block wrapped in the `LnFloorCert` namespace (each error-cert
literal is written to its own self-contained module). -/
def litText (name : String) (c : List Int) : String :=
  "namespace LnFloorCert\n\n" ++ Common.GenCover.litText name c ++ "end LnFloorCert\n"

end GenErrLit
open GenErrLit
def loLT : Int := 39614081257132168796771975168
def hiLT : Int := 56022770974786139918731938181
def loGE : Int := 56022770974786139918731938273
def hiGE : Int := 79228162514264337593543950335

#eval do
  IO.FS.writeFile "LnProof/Cert/ErrCertLtLit.lean" (litText "certErrLtLit" (ptrim cLt))
  IO.FS.writeFile "LnProof/Cert/ErrCertGeLit.lean" (litText "certErrGeLit" (ptrim cGe))
  IO.println "literals written"
  emit "ErrCertLtLit" "certErrLtLit" "ErrCertLt" "ErrCertLtC" "errLt_cell" "errLt_nonneg" (ptrim cLt) loLT hiLT
  emit "ErrCertGeLit" "certErrGeLit" "ErrCertGe" "ErrCertGeC" "errGe_cell" "errGe_nonneg" (ptrim cGe) loGE hiGE

import LnProof.ErrorBoundCore
import LnProof.KroneckerShift

/-! Regenerate the error-bound cert literals (ErrCertLtLit / ErrCertGeLit) and
their covers for the new BIASc + boundNum.  Computes `certErrLt`/`certErrGe`
inline (mirroring the ErrCert*Bridge constructions) so it does not depend on the
bridges building, then walks the `checkCoverK` covers (literal signature, as the
committed `errLt_nonneg`/`errGe_nonneg` use). -/

open LnPoly LnFloorCert LnExp LnFloor LnGeneratedModel

namespace GenErrLit

def errLtK : Int := 63382530011411470074835160268800000001014120480182583521197362564300800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def errGeK : Int := 63382530011411470074835160268800000001014120480182583521197362564300800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def errLtW : Nat := 3550864962631813931471340474605602525086155208949182483393131823026194872971536101998892269735065570843009162547284327412750539715096996420696892912576537978470400000000000000000000000000000000000000000000000000000000000000000
def errGeW : Nat := 3550864962631813931471340474582576916379914473087859055802254161455235801988744087918340449892173785220415643810587383485229574106090956592771097999224589015530340352000000000000000000000000000000000000000000000000000000000000

def cLt : List Int :=
  polyAdd (polyScale ((errLtW : Int) * (fact 23 : Int)) (polyPow ltTDLit 23))
    (polyScale (-errLtK) (polyMul [1, 1]
      (polyAdd (polyScale 23 (polyMul (expPolyNum ltTNLit ltTDLit 22) ltTDLit))
        (polyScale 2 (polyPow ltTNLit 23)))))

def cGe : List Int :=
  expMarginPoly 22 geTN2bLit geTD2bLit (polyScale errGeK [1, 1]) errGeW

/-- Drop trailing zero coefficients (mirror gen_cert_literals.ptrim). -/
def ptrim (a : List Int) : List Int :=
  let r := (a.reverse.dropWhile (· == 0)).reverse
  if r.isEmpty then [0] else r

partial def maxW (S : List Int) (hiW : Int) : Int :=
  let rec bs (lo hi : Int) : Int :=
    if lo ≥ hi then lo
    else let mid := (lo + hi + 1) / 2
         if 0 ≤ (hornerIv S 0 mid).1 then bs mid hi else bs lo (mid - 1)
  bs 0 hiW
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

def emit (litFile litName modPrefix cellPrefix nonnegName : String) (C : List Int) (lo hi : Int) : IO Unit := do
  let (ok, cells) := walk C lo hi
  IO.println s!"-- {nonnegName}: reached={ok} ncells={cells.length}"
  if ! ok then IO.println s!"-- FAILED tail: {cells.drop (cells.length-2)}"; return
  for (aw, i) in cells.zipIdx do
    let (a, w) := aw
    IO.FS.writeFile s!"LnProof/{modPrefix}{pad2 i}.lean"
      s!"import LnProof.{litFile}\nimport LnProof.KroneckerShift\n\nnamespace LnFloorCert\nopen LnPoly\n\nset_option maxRecDepth 100000\n\ntheorem {cellPrefix}{pad2 i} : checkCoverK kB {litName} {a} {a + w}\n    [{w}] = true := by\n  decide +kernel\n\nend LnFloorCert\n"
  IO.println "==== IMPORTS ===="
  for (_, i) in cells.zipIdx do IO.println s!"import LnProof.{modPrefix}{pad2 i}"
  IO.println "==== LADDER ===="
  let lb := "{"; let rb := "}"
  IO.println s!"theorem {nonnegName} {lb}m : Int{rb} (h1 : {lo} ≤ m) (h2 : m ≤ {hi}) :"
  IO.println s!"    0 ≤ evalPoly {litName} m := by"
  let n := cells.length
  for (aw, i) in cells.zipIdx do
    let (a, w) := aw
    if i + 1 < n then
      IO.println s!"  rcases Int.lt_or_le m ({a + w} + 1) with h | h"
      IO.println s!"  · exact checkCoverK_sound _ _ _ _ _ {cellPrefix}{pad2 i} m (by omega) (by omega)"
    else
      IO.println s!"  exact checkCoverK_sound _ _ _ _ _ {cellPrefix}{pad2 i} m (by omega) h2"

def litText (name : String) (c : List Int) : String :=
  "namespace LnFloorCert\n\ndef " ++ name ++ " : List Int := [\n  " ++
  String.intercalate ",\n  " (c.map toString) ++ "]\n\nend LnFloorCert\n"

end GenErrLit
open GenErrLit
def loLT : Int := 39614081257132168796771975168
def hiLT : Int := 56022770974786139918731938181
def loGE : Int := 56022770974786139918731938273
def hiGE : Int := 79228162514264337593543950335

#eval do
  IO.FS.writeFile "LnProof/ErrCertLtLit.lean" (litText "certErrLtLit" (ptrim cLt))
  IO.FS.writeFile "LnProof/ErrCertGeLit.lean" (litText "certErrGeLit" (ptrim cGe))
  IO.println "literals written"
  emit "ErrCertLtLit" "certErrLtLit" "ErrCertLtC" "errLt_cell" "errLt_nonneg" (ptrim cLt) loLT hiLT
  emit "ErrCertGeLit" "certErrGeLit" "ErrCertGeC" "errGe_cell" "errGe_nonneg" (ptrim cGe) loGE hiGE

import Common.Foundation.KroneckerShift

/-!
# Shared cover-certificate generator helpers

Helpers common to the `lake env lean Gen*.lean` certificate generators: trailing-zero trimming,
the greedy `checkCoverK` cell walk (binary-searching each cell's maximal width), the literal-list
emitter, and the cover-cell / `_nonneg`-ladder text templates. Everything here is generator-side
string/IO tooling; the in-kernel predicates it targets (`checkCoverK`, `checkCoverK_sound`) live
in `Common.Foundation.KroneckerShift`.
-/

namespace Common.GenCover

open Common.Poly

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

/-- Zero-padded two-digit index. -/
def pad2 (i : Nat) : String := (if i < 10 then "0" else "") ++ toString i

/-- One `def <name> : List Int := [...]` literal block. -/
def litText (name : String) (c : List Int) : String :=
  "def " ++ name ++ " : List Int := [\n  " ++
    String.intercalate ",\n  " (c.map toString) ++ "]\n\n"

/-- One cover-cell module: the kernel-decided `checkCoverK` theorem for `[a, a + w]`. -/
def cellText (importMod ns cellName litName : String) (a w : Int) : String :=
  s!"import {importMod}\nimport Common.Foundation.KroneckerShift\n\nnamespace {ns}\nopen Common.Poly\n\nset_option maxRecDepth 100000\n\ntheorem {cellName} : checkCoverK kB {litName} {a} {a + w}\n    [{w}] = true := by\n  decide +kernel\n\nend {ns}\n"

/-- One `_nonneg`-ladder step dispatching variable `x` into cell `cellName`; the final cell
consumes the ladder's upper hypothesis `h2` directly. -/
def ladderStep (cellName x : String) (a w : Int) (last : Bool) : String :=
  if last then
    s!"  exact checkCoverK_sound _ _ _ _ _ {cellName} {x} (by omega) h2\n"
  else
    s!"  rcases Int.lt_or_le {x} ({a + w} + 1) with h | h\n  · exact checkCoverK_sound _ _ _ _ _ {cellName} {x} (by omega) (by omega)\n"

end Common.GenCover

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

structure CellSpec where
  lo : Int
  hi : Int
  bits : Nat

structure CellEmitter where
  checkerImport : String
  preamble : String → String
  checkType : String → String → CellSpec → String
  soundTerm : String → String → CellSpec → String

/-- Search a finite consecutive range for its first checker-accepted bit width. -/
def firstAcceptedB (check : Nat → Bool) : Nat → Nat → Option Nat
  | _, 0 => none
  | start, fuel + 1 =>
    if check start then some start else firstAcceptedB check (start + 1) fuel

def strictPow2Bits (n : Nat) : Nat :=
  if n = 0 then 0 else Nat.log2 n + 1

def firstCoverKB (C : List Int) (lo hi : Int) (fuel : Nat) : Option Nat :=
  let start := strictPow2Bits (aeval C (1 + lo.natAbs) * 2)
  firstAcceptedB (fun B => checkCoverK B C lo hi [hi - lo]) start fuel

def acceptedKCell (C : List Int) (bitFuel : Nat) (lo hi : Int) : Option CellSpec :=
  match firstCoverKB C lo hi bitFuel with
  | none => none
  | some B => some ⟨lo, hi, B⟩

partial def bisectWidestK (C : List Int) (bitFuel : Nat)
    (accepted : CellSpec) (rejected : Int) : CellSpec :=
  if rejected ≤ accepted.hi + 1 then accepted
  else
    let mid := accepted.hi + (rejected - accepted.hi) / 2
    match acceptedKCell C bitFuel accepted.lo mid with
    | some cell => bisectWidestK C bitFuel cell rejected
    | none => bisectWidestK C bitFuel accepted mid

def widestKCell (C : List Int) (bitFuel : Nat) (lo hi : Int) : Option CellSpec :=
  if hi < lo then none
  else
    match acceptedKCell C bitFuel lo hi with
    | some full => some full
    | none =>
      match acceptedKCell C bitFuel lo lo with
      | none => none
      | some point => some (bisectWidestK C bitFuel point hi)

/-- Greedy left-to-right partition with a checker-accepted bit width per cell. -/
def walkK (C : List Int) (bitFuel : Nat) :
    Nat → Int → Int → Option (List CellSpec)
  | 0, lo, hi => if hi < lo then some [] else none
  | cellFuel + 1, lo, hi =>
    if hi < lo then some []
    else
      match widestKCell C bitFuel lo hi with
      | none => none
      | some cell =>
        if cell.hi = hi then some [cell]
        else
          match walkK C bitFuel cellFuel (cell.hi + 1) hi with
          | none => none
          | some rest => some (cell :: rest)

/-- Remove stale generated Lean files only from the caller's owned prefixes. -/
def reconcileOutputs (outDir : System.FilePath) (ownedPrefixes expected : List String) :
    IO Unit := do
  for entry in (← outDir.readDir) do
    let name := entry.fileName
    let owned := ownedPrefixes.any (fun pfx => name.startsWith pfx)
    let keep := expected.any (fun expectedName => name = expectedName)
    if name.endsWith ".lean" && owned && !keep then
      let metadata ← entry.path.symlinkMetadata
      if metadata.type == .file then
        IO.FS.removeFile entry.path

def cellTextWith (emitter : CellEmitter) (importMod ns cellName litName : String)
    (spec : CellSpec) : String :=
  s!"import {importMod}\nimport {emitter.checkerImport}\n\nnamespace {ns}\nopen Common.Poly\n\nset_option maxRecDepth 100000\n\n{emitter.preamble cellName}theorem {cellName} : {emitter.checkType litName cellName spec} := by\n  decide +kernel\n\ntheorem {cellName}_nonnegOn : NonnegOn {litName} {spec.lo} {spec.hi} := by\n  exact {emitter.soundTerm litName cellName spec}\n\nend {ns}\n"

def coverKEmitter : CellEmitter where
  checkerImport := "Common.Foundation.KroneckerShift"
  preamble := fun _ => ""
  checkType := fun litName _ spec =>
    s!"checkCoverK {spec.bits} {litName} {spec.lo} {spec.hi}\n    [{spec.hi - spec.lo}] = true"
  soundTerm := fun litName cellName spec =>
    s!"checkCoverK_nonnegOn {spec.bits} {litName} [{spec.hi - spec.lo}] {spec.lo} {spec.hi} {cellName}"

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

def cellTextK (importMod ns cellName litName : String) (spec : CellSpec) : String :=
  cellTextWith coverKEmitter importMod ns cellName litName spec

def emitKCells (outDir importMod ns modPrefix cellPrefix litName : String)
    (cells : List CellSpec) : IO Unit := do
  for (spec, i) in cells.zipIdx do
    let suffix := pad2 i
    IO.FS.writeFile s!"{outDir}/{modPrefix}{suffix}.lean"
      (cellTextK importMod ns s!"{cellPrefix}{suffix}" litName spec)

def walkAndEmitK (outDir importMod ns modPrefix cellPrefix litName : String)
    (C : List Int) (lo hi : Int) (cellFuel bitFuel : Nat) :
    IO (Option (List CellSpec)) := do
  let result := walkK C bitFuel cellFuel lo hi
  match result with
  | none => pure none
  | some cells =>
    let expected := cells.zipIdx.map fun (_, i) => s!"{modPrefix}{pad2 i}.lean"
    reconcileOutputs outDir [modPrefix] expected
    emitKCells outDir importMod ns modPrefix cellPrefix litName cells
    pure (some cells)

/-- One `_nonneg`-ladder step dispatching variable `x` into cell `cellName`; the final cell
consumes the ladder's upper hypothesis `h2` directly. -/
def ladderStep (cellName x : String) (a w : Int) (last : Bool) : String :=
  if last then
    s!"  exact checkCoverK_sound _ _ _ _ _ {cellName} {x} (by omega) h2\n"
  else
    s!"  rcases Int.lt_or_le {x} ({a + w} + 1) with h | h\n  · exact checkCoverK_sound _ _ _ _ _ {cellName} {x} (by omega) (by omega)\n"

end Common.GenCover

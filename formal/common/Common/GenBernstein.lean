import Common.Foundation.Bernstein
import Common.GenCover

/-!
# Bernstein certificate generation

The generator searches exact checker results and emits cell endpoints, bit
widths, and explicit weights. Generated modules remain independently checked
by Lean's kernel.
-/

namespace Common.GenBernstein

open Common.Poly Common.GenCover

structure BernsteinCell where
  spec : CellSpec
  weights : List Int

def weightsText (name : String) (weights : List Int) : String :=
  "def " ++ name ++ " : List Int := [\n  " ++
    String.intercalate ",\n  " (weights.map toString) ++ "]\n\n"

def bernsteinEmitter (weights : List Int) : CellEmitter where
  checkerImport := "Common.Foundation.Bernstein"
  preamble := fun cellName => weightsText s!"{cellName}Weights" weights
  checkType := fun litName cellName spec =>
    s!"checkBernsteinKWithWitness {spec.bits} {litName} {spec.lo} {spec.hi} {cellName}Weights = true"
  soundTerm := fun litName cellName spec =>
    s!"checkBernsteinKWithWitness_nonnegOn {spec.bits} {litName} {spec.lo} {spec.hi} {cellName}Weights {cellName}"

def generatedWeights (C : List Int) (a b : Int) : List Int :=
  let n := C.length - 1
  let q := scaleVariable (b - a) (polyShiftM C a)
  (List.range C.length).map (bernsteinWeight q n)

def bernsteinIdentityStart (C : List Int) (a b : Int) (weights : List Int) : Nat :=
  let n := C.length - 1
  max
    (strictPow2Bits (polyL1 (polyScale ((b - a) ^ n) C) * 2))
    (strictPow2Bits (bernsteinCertL1 a b n 0 weights * 2))

def weightsNonnegative (weights : List Int) : Bool :=
  decide (∀ d ∈ weights, 0 ≤ d)

/-- Find the first identity width that makes the exact checker accept a cell. -/
def firstBernsteinBWithWeights (C : List Int) (a b : Int) (weights : List Int)
    (fuel : Nat) : Option Nat :=
  if a < b && weightsNonnegative weights then
    let start := bernsteinIdentityStart C a b weights
    firstAcceptedB (fun B => checkBernsteinKWithWitness B C a b weights) start fuel
  else none

def firstBernsteinB (C : List Int) (a b : Int) (fuel : Nat) : Option Nat :=
  firstBernsteinBWithWeights C a b (generatedWeights C a b) fuel

def acceptedCell (C : List Int) (bitFuel : Nat) (lo hi : Int) : Option BernsteinCell :=
  let weights := generatedWeights C lo hi
  match firstBernsteinBWithWeights C lo hi weights bitFuel with
  | none => none
  | some B => some ⟨⟨lo, hi, B⟩, weights⟩

partial def bisectWidest (C : List Int) (bitFuel : Nat)
    (accepted : BernsteinCell) (rejected : Int) : BernsteinCell :=
  if rejected ≤ accepted.spec.hi + 1 then accepted
  else
    let mid := accepted.spec.hi + (rejected - accepted.spec.hi) / 2
    match acceptedCell C bitFuel accepted.spec.lo mid with
    | some cell => bisectWidest C bitFuel cell rejected
    | none => bisectWidest C bitFuel accepted mid

/-- The checker-accepted cell with the largest endpoint at the given anchor. -/
def widestCell (C : List Int) (bitFuel : Nat) (lo hi : Int) : Option BernsteinCell :=
  if hi ≤ lo then none
  else
    match acceptedCell C bitFuel lo (lo + 1) with
    | none => none
    | some first =>
      if hi = lo + 1 then some first
      else
        match acceptedCell C bitFuel lo hi with
        | some full => some full
        | none => some (bisectWidest C bitFuel first hi)

/-- Greedy left-to-right partition into the widest checker-accepted cells. -/
def search (C : List Int) (bitFuel : Nat) :
    Nat → Int → Int → Option (List BernsteinCell)
  | 0, lo, hi => if hi < lo then some [] else none
  | cellFuel + 1, lo, hi =>
    if hi < lo then some []
    else
      match widestCell C bitFuel lo hi with
      | none => none
      | some cell =>
        if cell.spec.hi = hi then some [cell]
        else
          match search C bitFuel cellFuel (cell.spec.hi + 1) hi with
          | none => none
          | some rest => some (cell :: rest)

def cellText (importMod ns cellName litName : String) (cell : BernsteinCell) : String :=
  cellTextWith (bernsteinEmitter cell.weights) importMod ns cellName litName cell.spec

def emitCells (outDir importMod ns modPrefix cellPrefix litName : String)
    (cells : List BernsteinCell) : IO Unit := do
  for (cell, i) in cells.zipIdx do
    let suffix := pad2 i
    IO.FS.writeFile s!"{outDir}/{modPrefix}{suffix}.lean"
      (cellText importMod ns s!"{cellPrefix}{suffix}" litName cell)

def searchAndEmit (outDir importMod ns modPrefix cellPrefix litName : String)
    (C : List Int) (lo hi : Int) (cellFuel bitFuel : Nat) :
    IO (Option (List BernsteinCell)) := do
  let result := search C bitFuel cellFuel lo hi
  match result with
  | none => pure none
  | some cells =>
    let expected := cells.zipIdx.map fun (_, i) => s!"{modPrefix}{pad2 i}.lean"
    reconcileOutputs outDir [modPrefix] expected
    emitCells outDir importMod ns modPrefix cellPrefix litName cells
    pure (some cells)

end Common.GenBernstein

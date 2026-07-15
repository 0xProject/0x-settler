import LnProof.Floor.CarryIndependent.Approximation
import Common.GenBernstein

open Common.Poly Common.GenBernstein Common.GenCover

namespace GenApproximationCert

set_option maxRecDepth 100000

inductive Family where
  | low
  | high

inductive CellKind where
  | horner
  | bernstein

structure CellMeta where
  family : Family
  index : Nat
  lo : Nat
  hi : Nat
  candidate : Nat
  kind : CellKind
  artifactLength : Nat

def dependencyLaneCount : Option Nat := some 4

def totalCellCount : Nat := 310
def lowCellCount : Nat := 131
def highCellCount : Nat := 179
def lowBernsteinIndices : List Nat := [6, 7, 55, 56, 91, 92, 114, 115, 116]
def highBernsteinIndices : List Nat := [0, 93, 94, 130, 131, 156, 157, 158, 174, 175]

def candidateAt (hi : Nat) : Nat :=
  Nat.sqrt (LnFloorCarry.approximationEnvelopeSquareBudget / (hi + 1))

def certificate (family : Family) (a : Nat) : List Int :=
  match family with
  | .low => LnFloorCarry.approximationLowCert a
  | .high => LnFloorCarry.approximationHighCert a

def familyStem : Family → String
  | .low => "Low"
  | .high => "High"

def familyCoverName : Family → String
  | .low => "approximationLowCover"
  | .high => "approximationHighCover"

def familyCertName : Family → String
  | .low => "approximationLowCert"
  | .high => "approximationHighCert"

def pad3 (i : Nat) : String :=
  (if i < 10 then "00" else if i < 100 then "0" else "") ++ toString i

def cellModuleName (family : Family) (index : Nat) : String :=
  s!"Approximation{familyStem family}C{pad3 index}"

def cellName (family : Family) (index : Nat) : String :=
  s!"approximation{familyStem family}Cell{pad3 index}"

def parentRange (i : Nat) : Nat × Nat :=
  let U := LnFloorCarry.approximationMaxU
  let lo := U * i / 64
  let hi := if i = 63 then U else U * (i + 1) / 64 - 1
  (lo, hi)

def tryCell (family : Family) (lo hi : Nat) : Option BernsteinCell :=
  acceptedCell (certificate family (candidateAt hi)) 128 lo hi

partial def split (family : Family) : Nat → Nat → Nat → Option (List BernsteinCell)
  | 0, _, _ => none
  | fuel + 1, lo, hi =>
      match tryCell family lo hi with
      | some cell => some [cell]
      | none =>
          if hi ≤ lo + 1 then none
          else
            let mid := (lo + hi) / 2
            match split family fuel lo mid, split family fuel (mid + 1) hi with
            | some lhs, some rhs => some (lhs ++ rhs)
            | _, _ => none

def allCells (family : Family) : Option (List BernsteinCell) :=
  (List.range 64).foldlM (init := []) fun acc i => do
    let (lo, hi) := parentRange i
    let cells ← split family 12 lo hi
    pure (acc ++ cells)

def packedBits (C shifted : List Int) (lo : Int) : Nat :=
  max
    (strictPow2Bits (polyL1 shifted * 2))
    (strictPow2Bits (aeval C (1 + lo.natAbs) * 2))

def laneStarts (laneCount : Nat) : List Nat :=
  (List.range laneCount).map fun i => totalCellCount * i / laneCount

def laneTips (laneCount : Nat) : List Nat :=
  (List.range laneCount).map fun i => totalCellCount * (i + 1) / laneCount - 1

def isLaneStart (laneCount index : Nat) : Bool :=
  (laneStarts laneCount).contains index

def familyAndIndex (globalIndex : Nat) : Family × Nat :=
  if globalIndex < lowCellCount then (.low, globalIndex)
  else (.high, globalIndex - lowCellCount)

def importText (laneCount globalIndex : Nat) : String :=
  if isLaneStart laneCount globalIndex then
    "import LnProof.Floor.CarryIndependent.Approximation\n"
  else
    let (family, index) := familyAndIndex (globalIndex - 1)
    s!"import LnProof.Cert.{cellModuleName family index}\n"

def sourceText (family : Family) (candidate : Nat) : String :=
  s!"{familyCertName family} {candidate}"

def hornerCellText (laneCount globalIndex : Nat) (family : Family)
    (index : Nat) (cell : BernsteinCell) (candidate bits : Nat)
    (shifted : List Int) : String :=
  let stem := cellName family index
  let source := sourceText family candidate
  let lo := cell.spec.lo
  let hi := cell.spec.hi
  let width := hi - lo
  importText laneCount globalIndex ++
    "import Common.Foundation.PackedShift\n\n" ++
    "namespace LnFloorCarry\n\n" ++
    "open Common.Poly\n\n" ++
    "set_option maxRecDepth 100000\n" ++
    s!"set_option exponentiation.threshold {bits}\n\n" ++
    litText s!"{stem}Shifted" shifted ++
    s!"theorem {stem}Candidate :\n" ++
    s!"    approximationEnvelopeCandidate {hi} {candidate} := by\n" ++
    s!"  change {candidate} ^ 2 * ({hi} + 1) ≤ approximationEnvelopeSquareBudget\n" ++
    "  decide +kernel\n\n" ++
    s!"theorem {stem}Radix :\n" ++
    s!"    evalPoly {stem}Shifted (((2 ^ {bits} : Nat) : Int)) =\n" ++
    s!"      evalPoly ({source})\n" ++
    s!"        ({lo} + (((2 ^ {bits} : Nat) : Int))) := by\n" ++
    "  decide +kernel\n\n" ++
    s!"theorem {stem}ScalarCheck :\n" ++
    s!"    checkPackedShiftScalars {bits}\n" ++
    s!"      (literalPackedShiftScalars {bits} ({source})\n" ++
    s!"        {stem}Shifted {lo}) = true := by\n" ++
    "  decide +kernel\n\n" ++
    s!"theorem {stem}HornerCheck :\n" ++
    s!"    decide (0 ≤ (hornerIv {stem}Shifted 0 {width}).1) = true := by\n" ++
    "  decide +kernel\n\n" ++
    s!"theorem {stem}Check :\n" ++
    s!"    checkPackedCell {bits} {stem}Shifted {width}\n" ++
    s!"      (literalPackedShiftScalars {bits} ({source})\n" ++
    s!"        {stem}Shifted {lo}) = true := by\n" ++
    "  simp only [checkPackedCell, Bool.and_eq_true]\n" ++
    s!"  exact ⟨⟨{stem}ScalarCheck, by decide +kernel⟩,\n" ++
    s!"    {stem}HornerCheck⟩\n\n" ++
    s!"theorem {stem}NonnegOn :\n" ++
    s!"    NonnegOn ({source}) {lo} {hi} := by\n" ++
    s!"  have hevidence := literalPackedShiftEvidence {stem}Radix\n" ++
    s!"  simpa using checkPackedCell_nonnegOn hevidence {stem}Check\n\n" ++
    "end LnFloorCarry\n"

def bernsteinCellText (laneCount globalIndex : Nat) (family : Family)
    (index : Nat) (cell : BernsteinCell) (candidate : Nat) : String :=
  let stem := cellName family index
  let source := sourceText family candidate
  let lo := cell.spec.lo
  let hi := cell.spec.hi
  importText laneCount globalIndex ++
    "import Common.Foundation.Bernstein\n\n" ++
    "namespace LnFloorCarry\n\n" ++
    "open Common.Poly\n\n" ++
    "set_option maxRecDepth 100000\n\n" ++
    weightsText s!"{stem}Weights" cell.weights ++
    s!"theorem {stem}Candidate :\n" ++
    s!"    approximationEnvelopeCandidate {hi} {candidate} := by\n" ++
    s!"  change {candidate} ^ 2 * ({hi} + 1) ≤ approximationEnvelopeSquareBudget\n" ++
    "  decide +kernel\n\n" ++
    s!"theorem {stem}Check :\n" ++
    s!"    checkBernsteinKWithWitness {cell.spec.bits} ({source})\n" ++
    s!"      {lo} {hi} {stem}Weights = true := by\n" ++
    "  decide +kernel\n\n" ++
    s!"theorem {stem}NonnegOn :\n" ++
    s!"    NonnegOn ({source}) {lo} {hi} :=\n" ++
    s!"  checkBernsteinKWithWitness_nonnegOn {cell.spec.bits} ({source})\n" ++
    s!"    {lo} {hi} {stem}Weights {stem}Check\n\n" ++
    "end LnFloorCarry\n"

def emitCell (outDir : System.FilePath) (laneCount globalIndex : Nat)
    (family : Family) (index : Nat) (cell : BernsteinCell) : IO CellMeta := do
  let lo := cell.spec.lo.toNat
  let hi := cell.spec.hi.toNat
  let candidate := candidateAt hi
  let C := certificate family candidate
  let shifted := polyShiftM C cell.spec.lo
  let horner := decide (0 ≤ (hornerIv shifted 0 (cell.spec.hi - cell.spec.lo)).1)
  let kind := if horner then CellKind.horner else CellKind.bernstein
  let text := if horner then
      hornerCellText laneCount globalIndex family index cell candidate
        (packedBits C shifted cell.spec.lo) shifted
    else
      bernsteinCellText laneCount globalIndex family index cell candidate
  IO.FS.writeFile (outDir / s!"{cellModuleName family index}.lean") text
  let artifactLength := if horner then shifted.length else cell.weights.length
  pure ⟨family, index, lo, hi, candidate, kind, artifactLength⟩

def emitFamily (outDir : System.FilePath) (laneCount globalOffset : Nat)
    (family : Family) (cells : List BernsteinCell) : IO (List CellMeta) := do
  let mut result := []
  for (cell, index) in cells.zipIdx do
    let cellMeta ← emitCell outDir laneCount (globalOffset + index) family index cell
    result := cellMeta :: result
  pure result.reverse

def bernsteinIndices (cells : List CellMeta) : List Nat :=
  cells.filterMap fun cell =>
    match cell.kind with
    | .horner => none
    | .bernstein => some cell.index

def contiguousCover : Nat → List CellMeta → Bool
  | next, [] => next == LnFloorCarry.approximationMaxU + 1
  | next, cell :: cells =>
      cell.lo == next && contiguousCover (cell.hi + 1) cells

def aggregateImports (laneCount : Nat) : String :=
  String.join <| (laneTips laneCount).map fun tip =>
    let (family, index) := familyAndIndex tip
    s!"import LnProof.Cert.{cellModuleName family index}\n"

def coverStep (cellMeta : CellMeta) (last : Bool) : String :=
  let stem := cellName cellMeta.family cellMeta.index
  let result :=
    s!"⟨{cellMeta.hi}, {cellMeta.candidate}, by omega, {stem}Candidate, " ++
      s!"{stem}NonnegOn (u : Int) (by exact_mod_cast hlo) " ++
      "(by exact_mod_cast hhi)⟩"
  if last then
    s!"  have hhi : u ≤ {cellMeta.hi} := by simpa [approximationMaxU] using hu\n" ++
      s!"  exact {result}\n"
  else
    s!"  by_cases hhi : u ≤ {cellMeta.hi}\n" ++
      s!"  · exact {result}\n" ++
      s!"  have hlo : {cellMeta.hi + 1} ≤ u := by omega\n"

def coverText (family : Family) (cells : List CellMeta) : String :=
  let cert := familyCertName family
  let name := familyCoverName family
  let header :=
    s!"theorem {name} " ++ "{u : Nat}" ++
      " (hu : u ≤ approximationMaxU) :\n" ++
      s!"    ∃ hi a, u ≤ hi ∧ approximationEnvelopeCandidate hi a ∧\n" ++
      s!"      0 ≤ evalPoly ({cert} a) (u : Int) := by\n" ++
      "  have hlo : 0 ≤ u := Nat.zero_le u\n"
  let steps := String.join <| cells.zipIdx.map fun (cellMeta, i) =>
    coverStep cellMeta (i + 1 == cells.length)
  header ++ steps ++ "\n"

def aggregateText (laneCount : Nat) (low high : List CellMeta) : String :=
  aggregateImports laneCount ++
    "\nnamespace LnFloorCarry\n\n" ++
    "open Common.Poly\n\n" ++
    "set_option maxRecDepth 100000\n\n" ++
    coverText .low low ++ coverText .high high ++
    "end LnFloorCarry\n"

def hornerCorrelationPErrorNum : List Int :=
  [2 ^ 274, 2 ^ 187, 2 ^ 90, 1]

def hornerCorrelationDErrorNum : List Int :=
  [2 ^ 273, 2 ^ 178, 2 ^ 90, 1]

def hornerCorrelationDNum : List Int := polyNeg LnYul.QQc

def hornerCorrelationNum : List Int :=
  polyScale (2 ^ 112) <|
    polyAdd
      (polyScale (2 ^ 29)
        (polyMul LnYul.PPc hornerCorrelationDErrorNum))
      (polyMul hornerCorrelationPErrorNum hornerCorrelationDNum)

def hornerCorrelationDen : List Int :=
  polyMul hornerCorrelationDNum
    (polyAdd hornerCorrelationDNum
      (polyScale (2 ^ 113) hornerCorrelationDErrorNum))

def hornerCorrelationEndpointNum : Int :=
  evalPoly hornerCorrelationNum (LnYul.Uc : Int)

def hornerCorrelationEndpointDen : Int :=
  evalPoly hornerCorrelationDen (LnYul.Uc : Int)

def hornerCorrelationCert : List Int :=
  polyAdd
    (polyScale hornerCorrelationEndpointNum hornerCorrelationDen)
    (polyScale (-hornerCorrelationEndpointDen) hornerCorrelationNum)

def correlationDefinitionsText : String :=
  "def hornerCorrelationPErrorNum : List Int :=\n" ++
      "  [2 ^ 274, 2 ^ 187, 2 ^ 90, 1]\n\n" ++
      "def hornerCorrelationDErrorNum : List Int :=\n" ++
      "  [2 ^ 273, 2 ^ 178, 2 ^ 90, 1]\n\n" ++
      "def hornerCorrelationDNum : List Int := polyNeg QQc\n\n" ++
      "def hornerCorrelationNum : List Int :=\n" ++
      "  polyScale (2 ^ 112) <|\n" ++
      "    polyAdd\n" ++
      "      (polyScale (2 ^ 29)\n" ++
      "        (polyMul PPc hornerCorrelationDErrorNum))\n" ++
      "      (polyMul hornerCorrelationPErrorNum hornerCorrelationDNum)\n\n" ++
      "def hornerCorrelationDen : List Int :=\n" ++
      "  polyMul hornerCorrelationDNum\n" ++
      "    (polyAdd hornerCorrelationDNum\n" ++
      "      (polyScale (2 ^ 113) hornerCorrelationDErrorNum))\n\n"

def hornerCorrelationText (bits : Nat) (weights : List Int) : String :=
  "import LnProof.Model.Body\n" ++
    "import Common.Foundation.Bernstein\n\n" ++
    "namespace LnFloorCarry\n\n" ++
    "open Common.Poly LnYul\n\n" ++
    "set_option maxRecDepth 100000\n\n" ++
    correlationDefinitionsText ++
    "def endpointNum : Int := evalPoly hornerCorrelationNum (Uc : Int)\n" ++
    "def endpointDen : Int := evalPoly hornerCorrelationDen (Uc : Int)\n\n" ++
    "def hornerCorrelationCert : List Int :=\n" ++
    "  polyAdd (polyScale endpointNum hornerCorrelationDen)\n" ++
    "    (polyScale (-endpointDen) hornerCorrelationNum)\n\n" ++
    weightsText "hornerCorrelationWeights" weights ++
    "theorem hornerCorrelationCheck :\n" ++
    s!"    checkBernsteinKWithWitness {bits} hornerCorrelationCert\n" ++
    "      0 (Uc : Int) hornerCorrelationWeights = true := by\n" ++
    "  decide +kernel\n\n" ++
    "theorem hornerCorrelation_nonnegOn :\n" ++
    "    NonnegOn hornerCorrelationCert 0 (Uc : Int) :=\n" ++
    s!"  checkBernsteinKWithWitness_nonnegOn {bits} hornerCorrelationCert\n" ++
    "    0 (Uc : Int) hornerCorrelationWeights hornerCorrelationCheck\n\n" ++
    "theorem hornerCorrelationCert_eval (u : Int) :\n" ++
    "    evalPoly hornerCorrelationCert u =\n" ++
    "      endpointNum * evalPoly hornerCorrelationDen u -\n" ++
    "        endpointDen * evalPoly hornerCorrelationNum u := by\n" ++
    "  simp only [hornerCorrelationCert, evalPoly_polyAdd, evalPoly_polyScale]\n" ++
    "  ring\n\n" ++
    "theorem hornerCorrelation_nonneg {u : Int}\n" ++
    "    (hlo : 0 ≤ u) (hhi : u ≤ (Uc : Int)) :\n" ++
    "    0 ≤ evalPoly hornerCorrelationCert u :=\n" ++
    "  hornerCorrelation_nonnegOn u hlo hhi\n\n" ++
    "end LnFloorCarry\n"

def emitHornerCorrelation (outDir : System.FilePath) : IO Unit := do
  let weights := generatedWeights hornerCorrelationCert 0 LnYul.Uc
  let some bits := firstBernsteinBWithWeights hornerCorrelationCert 0 LnYul.Uc weights 128
    | throw (IO.userError "Horner-correlation certificate was rejected")
  IO.FS.writeFile (outDir / "HornerCorrelation.lean")
    (hornerCorrelationText bits weights)

def expectedOutputs : List String :=
  (List.range lowCellCount).map (fun i => s!"{cellModuleName .low i}.lean") ++
  (List.range highCellCount).map (fun i => s!"{cellModuleName .high i}.lean") ++
  ["Approximation.lean", "HornerCorrelation.lean"]

def generate (laneCount : Nat) : IO Unit := do
  unless laneCount == 2 || laneCount == 4 || laneCount == 8 do
    throw (IO.userError "dependencyLaneCount must be 2, 4, or 8")
  let outDir : System.FilePath := "LnProof/Cert"
  let some lowCells := allCells .low
    | throw (IO.userError "low approximation cover failed")
  unless lowCells.length == lowCellCount do
    throw (IO.userError s!"expected {lowCellCount} low cells, got {lowCells.length}")
  let low ← emitFamily outDir laneCount 0 .low lowCells
  let some highCells := allCells .high
    | throw (IO.userError "high approximation cover failed")
  unless highCells.length == highCellCount do
    throw (IO.userError s!"expected {highCellCount} high cells, got {highCells.length}")
  let high ← emitFamily outDir laneCount lowCellCount .high highCells
  unless contiguousCover 0 low do
    throw (IO.userError "low approximation cells are not contiguous")
  unless contiguousCover 0 high do
    throw (IO.userError "high approximation cells are not contiguous")
  unless bernsteinIndices low == lowBernsteinIndices do
    throw (IO.userError s!"unexpected low Bernstein cells: {bernsteinIndices low}")
  unless bernsteinIndices high == highBernsteinIndices do
    throw (IO.userError s!"unexpected high Bernstein cells: {bernsteinIndices high}")
  let hornerCount := (low ++ high).countP fun cell =>
    match cell.kind with
    | .horner => true
    | .bernstein => false
  unless hornerCount == 291 do
    throw (IO.userError s!"expected 291 Horner cells, got {hornerCount}")
  let literalCount := (low ++ high).foldl (fun n cell => n + cell.artifactLength) 0
  unless literalCount == 14701 do
    throw (IO.userError s!"expected 14701 coefficient literals, got {literalCount}")
  reconcileOutputs outDir
    ["ApproximationLowC", "ApproximationHighC", "Approximation.lean",
      "HornerCorrelation.lean"] expectedOutputs
  IO.FS.writeFile (outDir / "Approximation.lean")
    (aggregateText laneCount low high)
  emitHornerCorrelation outDir

def main : IO Unit :=
  match dependencyLaneCount with
  | none => throw (IO.userError "dependencyLaneCount is not selected")
  | some laneCount => generate laneCount

end GenApproximationCert

#eval GenApproximationCert.main

import LnProof.Error.Core.BranchCertHardDefs
import Common.GenCover

namespace GenBranchCertHard

open Common.GenCover

def outDir : String := "LnProof/Cert"
def chunkSize : Nat := 16
def caseCount : Nat := 159

def chunkCount : Nat := (caseCount + chunkSize - 1) / chunkSize

def chunkImport (chunk : Nat) : String :=
  if chunk = 0 ∨ chunk = chunkCount / 2 then
    "LnProof.Error.Core.BranchCertHardDefs"
  else
    s!"LnProof.Cert.HardMantissaLtGapC{pad2 (chunk - 1)}"

def chunkText (chunk start count : Nat) : String :=
  s!"import {chunkImport chunk}\n\nnamespace LnFloorCert\n\nset_option maxRecDepth 100000\n\ntheorem hardMantissaLtGapBranch_chunk{pad2 chunk} :\n    (List.range {count}).all (fun i => hardMantissaLtGapBranchB (i + {start})) = true := by\n  decide +kernel\n\nend LnFloorCert\n"

def aggregateText : String :=
  let cases := (List.range chunkCount).map fun chunk =>
    let offset := chunk * chunkSize
    let upper := min caseCount (offset + chunkSize)
    if offset = 0 then s!"i < {upper}" else s!"({offset} ≤ i ∧ i < {upper})"
  let caseProofs := (List.range chunkCount).map fun chunk =>
    s!"  · exact hardMantissaLtGapBranch_of_chunk hardMantissaLtGapBranch_chunk{pad2 chunk}\n      (by omega) (by omega)"
  s!"import LnProof.Cert.HardMantissaLtGapC04\nimport LnProof.Cert.HardMantissaLtGapC09\n\nnamespace LnFloorCert\n\nset_option maxRecDepth 100000\n\nprivate theorem hardMantissaLtGapBranch_of_chunk {lb}start count i : Nat{rb}\n    (hchunk : (List.range count).all\n      (fun j => hardMantissaLtGapBranchB (j + start)) = true)\n    (hlo : start ≤ i + 1) (hhi : i + 1 < start + count) :\n    hardMantissaLtGapBranchB (i + 1) = true := by\n  have h := List.all_eq_true.mp hchunk (i + 1 - start)\n    (List.mem_range.mpr (by omega))\n  rw [show i + 1 - start + start = i + 1 by omega] at h\n  exact h\n\ntheorem hardMantissaLtGapBranch_all :\n    (List.range {caseCount}).all (fun i => hardMantissaLtGapBranchB (i + 1)) = true := by\n  rw [List.all_eq_true]\n  intro i hi\n  have hlt : i < {caseCount} := List.mem_range.mp hi\n  have hcases :\n      {String.intercalate " ∨\n      " cases} := by\n    omega\n  rcases hcases with {String.intercalate " | " ((List.range chunkCount).map fun _ => "h")}\n{String.intercalate "\n" caseProofs}\n\nend LnFloorCert\n"
where
  lb := "{"
  rb := "}"

def expectedOutputs : List String :=
  "HardMantissaLtGap.lean" :: (List.range chunkCount).map fun i =>
    s!"HardMantissaLtGapC{pad2 i}.lean"

def generate : IO Unit := do
  reconcileOutputs outDir ["HardMantissaLtGap"] expectedOutputs
  let chunkOutputs := expectedOutputs.drop 1
  for (name, chunk) in chunkOutputs.zipIdx do
    let offset := chunk * chunkSize
    let count := min chunkSize (caseCount - offset)
    IO.FS.writeFile s!"{outDir}/{name}" (chunkText chunk (offset + 1) count)
  IO.FS.writeFile s!"{outDir}/HardMantissaLtGap.lean" aggregateText

end GenBranchCertHard

#eval GenBranchCertHard.generate

import SqrtProof

theorem proofLinked_innerSqrt_bracket_u256_all :
    ∀ x : Nat, x < 2 ^ 256 →
      let m := natSqrt x
      m ≤ innerSqrt x ∧ innerSqrt x ≤ m + 1 :=
  innerSqrt_bracket_u256_all

theorem proofLinked_floorSqrt_correct_u256 :
    ∀ x : Nat, x < 2 ^ 256 →
      let r := floorSqrt x
      r * r ≤ x ∧ x < (r + 1) * (r + 1) :=
  floorSqrt_correct_u256

def main : IO Unit := do
  IO.println "sqrtproof: linked to core theorems."
  IO.println "sqrtproof: run `lake build` to kernel-check the full proof development."

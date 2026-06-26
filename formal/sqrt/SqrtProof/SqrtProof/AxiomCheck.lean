import SqrtProof.SqrtYulCorrect

/-!
# Axiom gate

`#guard_msgs` pins the axiom dependency set of each public runtime correctness theorem.
The build fails if a proof starts depending on anything beyond Lean's standard
`propext`, `Classical.choice`, `Quot.sound` (in particular, a stray `sorry`
introduces `sorryAx` and breaks this gate).
-/

/-- info: 'SqrtYul.run_sqrt_floor_evm_eq_natSqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SqrtYul.run_sqrt_floor_evm_eq_natSqrt

/-- info: 'SqrtYul.run_sqrt_up_evm_eq_sqrtUp256' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SqrtYul.run_sqrt_up_evm_eq_sqrtUp256

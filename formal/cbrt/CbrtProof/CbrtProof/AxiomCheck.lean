import CbrtProof.CbrtYulCorrect

/-!
# Axiom gate

`#guard_msgs` pins the axiom dependency set of each public runtime correctness theorem.
The build fails if a proof starts depending on anything beyond Lean's standard
`propext`, `Classical.choice`, `Quot.sound` (in particular, a stray `sorry`
introduces `sorryAx` and breaks this gate).
-/

/-- info: 'CbrtYul.run_cbrt_floor_evm_eq_icbrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CbrtYul.run_cbrt_floor_evm_eq_icbrt

/-- info: 'CbrtYul.run_cbrt_up_evm_eq_cbrtUp256' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CbrtYul.run_cbrt_up_evm_eq_cbrtUp256

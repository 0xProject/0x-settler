import Sqrt512Proof.Sqrt512YulCorrect

/-!
# Axiom gate

`#guard_msgs` pins the axiom dependency set of each top-level correctness theorem.
The build fails if a proof starts depending on anything beyond Lean's standard
`propext`, `Classical.choice`, `Quot.sound` (in particular, a stray `sorry`
introduces `sorryAx` and breaks this gate).
-/

/-- info: 'Sqrt512Yul.run_sqrt512_wrapper_evm_eq_natSqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sqrt512Yul.run_sqrt512_wrapper_evm_eq_natSqrt

/-- info: 'Sqrt512Yul.run_osqrtUp_evm_eq_sqrtUp512Pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sqrt512Yul.run_osqrtUp_evm_eq_sqrtUp512Pair

import Cbrt512Proof.Cbrt512YulCorrect

/-!
# Axiom gate

`#guard_msgs` pins the axiom dependency set of each top-level correctness theorem.
The build fails if a proof starts depending on anything beyond Lean's standard
`propext`, `Classical.choice`, `Quot.sound` (in particular, a stray `sorry`
introduces `sorryAx` and breaks this gate).
-/

/-- info: 'Cbrt512Yul.run_cbrt512_wrapper_evm_eq_icbrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cbrt512Yul.run_cbrt512_wrapper_evm_eq_icbrt

/-- info: 'Cbrt512Yul.run_cbrtUp512_wrapper_evm_eq_cbrtUp512' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cbrt512Yul.run_cbrtUp512_wrapper_evm_eq_cbrtUp512

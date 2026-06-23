import LnProof.LnYulCorrect

/-!
# Axiom gate

`#guard_msgs` pins the axiom dependency set of the ln runtime surface. The build
fails if a proof starts depending on anything beyond Lean's standard `propext`,
`Classical.choice`, `Quot.sound` (in particular, a stray `sorry` introduces
`sorryAx` and breaks this gate).

Note: the `lnWad*RuntimeCorrect_of_cutCorrect` theorems are conditional on the
`CutCorrect` hypothesis, which is not yet discharged for the compiled code. This
gate pins their axiom dependency set; it does not assert unconditional correctness.
-/

/-- info: 'LnYul.lnWadToRayRuntimeCorrect_of_cutCorrect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LnYul.lnWadToRayRuntimeCorrect_of_cutCorrect

/-- info: 'LnYul.lnWadRuntimeCorrect_of_cutCorrect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LnYul.lnWadRuntimeCorrect_of_cutCorrect

/-- info: 'LnYul.run_ln_wad_evm_eq_callWord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LnYul.run_ln_wad_evm_eq_callWord

/-- info: 'LnYul.run_ln_wad_to_ray_evm_eq_callWord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LnYul.run_ln_wad_to_ray_evm_eq_callWord

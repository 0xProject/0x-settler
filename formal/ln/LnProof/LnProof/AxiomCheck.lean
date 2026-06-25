import LnProof.LnYulCorrect

/-!
# Axiom gate

`#guard_msgs in #print axioms` pins the axiom dependency set of each public ln
runtime theorem to Lean's standard `propext`, `Classical.choice`, `Quot.sound`.
The build fails if a proof starts depending on anything more — in particular a
stray `sorry` introduces `sorryAx` and breaks this gate.
-/

/-- info: 'LnYul.lnWadToRayRuntimeCorrect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LnYul.lnWadToRayRuntimeCorrect

/-- info: 'LnYul.lnWadRuntimeCorrect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LnYul.lnWadRuntimeCorrect

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

/-- info: 'LnYul.lnWadToRayRuntimeRevertsNonpositive_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LnYul.lnWadToRayRuntimeRevertsNonpositive_holds

/-- info: 'LnYul.lnWadRuntimeRevertsNonpositive_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LnYul.lnWadRuntimeRevertsNonpositive_holds

/-- info: 'LnYul.run_ln_wad_to_ray_evm_zero_at_wad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LnYul.run_ln_wad_to_ray_evm_zero_at_wad

/-- info: 'LnYul.lnWadToRayRuntimeNegativeIff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LnYul.lnWadToRayRuntimeNegativeIff

/-- info: 'LnYul.lnWadToRayRuntimeMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LnYul.lnWadToRayRuntimeMono

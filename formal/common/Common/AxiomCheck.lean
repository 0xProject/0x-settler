import Common.Foundation.KroneckerShift
import Common.Foundation.Bernstein

/-!
# Axiom gate

The public certificate soundness theorems must remain independent of
nonstandard axioms.
-/

/-- info: 'Common.Poly.checkCoverK_nonnegOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Common.Poly.checkCoverK_nonnegOn

/-- info: 'Common.Poly.checkBernsteinKWithWitness_nonnegOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Common.Poly.checkBernsteinKWithWitness_nonnegOn

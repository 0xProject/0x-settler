/-!
# Floor facade

The proof that the model meets the floor/cut specification. `Spec` is the
top-line floor-cut statement and its discharge (`lnWadToRayBody_floor`);
`CutEquiv` shows the floor spec coincides with the real-free `Spec.Cut`
predicates and that the model satisfies them. The supporting bracket/cap/cert
machinery lives in the rest of the `Floor/` directory.
-/
import LnProof.Floor.Spec
import LnProof.Floor.CutEquiv

/-!
# Spec facade

What "correct" means. `Real` is the public target — a fixed-point bracket
around `Real.log`. `Cut` is the real-free arithmetized restatement (exponential
Taylor cuts) the EVM-side proof actually discharges; the two are shown
equivalent by `Floor.CutEquiv` and `Seam.RealLog`.
-/
import LnProof.Spec.Real
import LnProof.Spec.Cut

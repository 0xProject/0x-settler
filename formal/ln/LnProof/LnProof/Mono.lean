/-!
# Mono facade

Monotonicity of the model over its whole domain. `Top` is the entry point
(`lnWadToRayBody_mono` / `lnWadBody_mono`); it composes the within-octave step
(`Step`, `ZOctave`, `Octave`, `Certs`) with the cross-`clz`-seam and
corrected-point cases (`Seams`).
-/
import LnProof.Mono.Top

import ExpProof.Mono.Top
import ExpProof.Mono.Octave
import ExpProof.Mono.Seam

/-!
# Mono facade

Monotonicity of the compiled `expRayToWad` runtime. `Top` is the entry point:
`expTree_mono` / `run_exp_ray_to_wad_evm_mono` reduce monotonicity over the whole supported domain
to the analytic facts on the meaningful region (`RegionMonotonicityFacts`), via the clamp/pin shell (`Shell`,
`ShellOn`) and the run-level bridge (`RunBridge`). `Octave` supplies the octave-index and
reduced-argument transports and their monotonicity; `WordMono` the word-level transports.
-/

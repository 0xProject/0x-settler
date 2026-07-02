import ExpProof.Mono.Top
import ExpProof.Floor.R0ExpUnder

/-!
# Discharging the octave-seam `r0`-doubling bound for monotonicity

`SeamR0Bound` (`r0Tree x1 + 2 ≤ 2·r0Tree x2` across one octave seam) is the single analytic
obligation that `run_exp_ray_to_wad_evm_mono_of_seamR0` carries. The per-point real bracket
`r0Tree x ≈ 2¹²⁶·exp(rt)` (`Floor.R0Exp`/`Floor.R0ExpUnder`, both signs) together with the seam
exp relation
`rt1 = rt2 + ln2 − 1/RAY` discharges it: `exp(rt1) = 2·exp(rt2)·exp(−1/RAY)`, and the
`1 − exp(−1/RAY) ≈ 1/RAY` slack (against `r0Tree x2 > 2¹²⁴`, worth `≈ 1.7·10¹¹` grid units)
dwarfs both the loose per-point envelope constants and the two integer units the seam-floor
comparison consumes. This closes `run_exp_ray_to_wad_evm_mono` without an external monotonicity
hypothesis.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation

/-- **The octave-seam `r0`-doubling bound holds.** -/
theorem seamR0Bound_holds : SeamR0Bound :=
  fun hx1 hx2 hC1 hC01 hC2 hC02 hk hadj =>
    r0_seam_double hx1 hx2 hC1 hC01 hC2 hC02 hk hadj

/-- **Runtime monotonicity, with the seam bound discharged.** -/
theorem run_exp_ray_to_wad_evm_mono_unconditional (x1 x2 : Nat)
    (hx1 : x1 < 2 ^ 256) (hx2 : x2 < 2 ^ 256)
    (hle : int256 x1 ≤ int256 x2) (hdom : int256 x2 < int256 C0thresh) :
    ∃ r1 r2, run_exp_ray_to_wad_evm x1 = .ok r1 ∧ run_exp_ray_to_wad_evm x2 = .ok r2 ∧
      int256 r1 ≤ int256 r2 :=
  run_exp_ray_to_wad_evm_mono_of_seamR0 seamR0Bound_holds x1 x2 hx1 hx2 hle hdom

end ExpYul

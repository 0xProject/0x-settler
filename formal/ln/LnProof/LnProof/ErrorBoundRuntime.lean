import LnProof.Correct
import LnProof.Error.Bound

/-!
# Runtime-level error bound

`LnFloorCert.lnWadToRayBody_error_bound_1_6986` proves the `1.6986`-ulp upper
error bound about the hand model `lnWadToRayBody`. This module transports that
bound to the compiled `lnWadToRay` runtime through the runtime↔model equality
`run_ln_wad_to_ray_evm_eq_body`, so the published bound holds for the
interpretation of the implementation, not just the model.

The conclusion is the real-free upper cut
`CutLogWadRayLtRational x r 1698600000 10^9`, the arithmetized counterpart of
`10^27·log(x/10^18) < r + 1698600000/10^9`.
-/

set_option maxRecDepth 100000

namespace LnYul

open FormalYul
open FormalYul.Preservation
open Common.Word

noncomputable section

-- `lnWadToRayBody` has a deep body (Horner pipeline); keep it opaque so the
-- `.2` projection below does not force whnf of `int256 (lnWadToRayBody x)`.
attribute [local irreducible] lnWadToRayBody

/-- The compiled `lnWadToRay` runtime satisfies the `1.6986`-ulp upper error
bound cut for every 256-bit positive signed input. The proof transports the
model bound `LnFloorCert.lnWadToRayBody_error_bound_1_6986` along the
runtime↔model equality. -/
theorem lnWadToRayRuntimeErrorBound (x : Nat) (hx : x < 2 ^ 256) :
    signedPositiveInput x →
      ∃ r, runLnWadToRaySigned x = .ok r ∧
        LnFloorCert.CutLogWadRayLtRational x r
          LnFloorCert.lnErrorBoundNum LnFloorCert.lnErrorBoundDen := by
  intro hxSigned
  obtain ⟨hpos, hpos2⟩ := u256_pos_bounds hxSigned
  have hux : u256 x = x := u256_eq_of_lt x (by simpa [WORD_MOD] using hx)
  have hrun := run_ln_wad_to_ray_evm_eq_body x hpos hpos2
  rw [hux] at hpos hpos2 hrun
  refine ⟨int256 (lnWadToRayBody x), ?_, ?_⟩
  · rw [runLnWadToRaySigned_ok_iff]
    refine ⟨lnWadToRayBody x, hrun, ?_⟩
    show int256 (u256 (lnWadToRayBody x)) = int256 (lnWadToRayBody x)
    rw [u256_eq_of_lt _ (by simpa [WORD_MOD] using lnWadToRayBody_lt hx)]
  · exact (LnFloorCert.lnWadToRayBody_error_bound_1_6986 hpos hpos2).2

end

end LnYul

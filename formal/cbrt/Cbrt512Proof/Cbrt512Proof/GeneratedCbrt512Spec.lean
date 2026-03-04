/-
  Bridge from model_cbrt512_evm to icbrt: specification layer.

  Part 1: EVM simplification lemmas (shared with wrapper/up specs).
  Part 2: Core algorithm bridge — model_cbrt512_evm within 1ulp of icbrt.
  Part 3: Composition with icbrt.

  Architecture: model_cbrt512_evm →[direct EVM bridge]→ icbrt ± 1

  Note: The auto-generated norm model (model_cbrt512) uses unbounded Nat operations
  which do NOT match EVM uint256 semantics. Therefore we prove the EVM model correct
  directly, without factoring through the norm model.
-/
import Cbrt512Proof.Cbrt512Correct
import Cbrt512Proof.GeneratedCbrt512Model
import Cbrt512Proof.CbrtDenormalization
import Cbrt512Proof.CbrtNormalization
import Cbrt512Proof.CbrtBaseCase
import Cbrt512Proof.CbrtKaratsubaQuotient
import Cbrt512Proof.CbrtComposition
import Cbrt512Proof.EvmBridge

namespace Cbrt512Spec

-- ============================================================================
-- Section 2: Core algorithm correctness
-- model_cbrt512_evm returns a value within 1ulp of icbrt for x_hi > 0.
-- ============================================================================

open Cbrt512GeneratedModel

/-- The 512-bit _cbrt EVM model returns a value within 1ulp of icbrt.
    For x_hi > 0 and both x_hi, x_lo < 2^256:
      icbrt(x_hi * 2^256 + x_lo) ≤ r ≤ icbrt(x_hi * 2^256 + x_lo) + 1
    and r < WORD_MOD, r³ < WORD_MOD² (so cube512_correct applies).
    Additionally, when r overshoots (r³ > x), x is not a perfect cube.
    This ensures the cbrtUp wrapper's cube-and-compare correction is sound. -/
theorem model_cbrt512_evm_within_1ulp (x_hi x_lo : Nat)
    (hxhi_pos : 0 < x_hi) (hxhi : x_hi < 2 ^ 256) (hxlo : x_lo < 2 ^ 256) :
    let x := x_hi * 2 ^ 256 + x_lo
    let r := model_cbrt512_evm x_hi x_lo
    icbrt x ≤ r ∧ r ≤ icbrt x + 1 ∧ r < WORD_MOD ∧ r * r * r < WORD_MOD * WORD_MOD
    ∧ r + 1 < WORD_MOD
    ∧ (r * r * r > x → icbrt x * icbrt x * icbrt x < x) := by
  /- Proof strategy:
     1. Compute shift = clz(x_hi)/3, normalize x → x_norm = x * 2^(3*shift)
     2. Use composition_within_1ulp on x_norm to get r_norm within 1ulp of icbrt(x_norm)
     3. Denormalize: r = r_norm >> shift gives icbrt(x) ≤ r ≤ icbrt(x) + 1
     4. Derive remaining bounds (r < W, r³ < W², r+1 < W, overshoot property)
  -/
  sorry

end Cbrt512Spec

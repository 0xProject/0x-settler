import LnProof.GeneratedLnModel

/-!
# Monotonicity certificates for the generated Ln model

`Ln.lnWad` maps a wad-basis input to a ray-basis `int256` encoded as a
two's-complement word, so ordering statements use the sign-bit-biased
unsigned comparison `sle`.

Monotonicity of `lnWad` over its whole domain `0 < x < 2^255` decomposes as:

* adjacent inputs that share the Q103 mantissa and exponent return the same
  word (the model is a function of the mantissa/exponent pair);
* within an octave, the mantissa-to-result map is nondecreasing -- this is
  the analytic certificate checked by exact rational arithmetic in
  `formal/python/ln/check_ln_monotone.py`;
* across the 254 clz seams, the adjacent pair `(2^t - 1, 2^t)` is decided
  here by kernel evaluation of the generated model;
* the single corrected point `x = 10^18` (whose exact result, 0, is the only
  integer value of the function) is decided here together with its
  neighbors.

The theorems in this file are the finitely-decidable legs of that argument,
evaluated against the same generated model that the FFI fuzz suite checks
against the deployed Solidity.
-/

set_option maxRecDepth 8192

namespace LnGeneratedModel

/-- Signed (two's complement) `≤` on uint256 words: unsigned comparison with
the sign bit flipped. -/
def sle (a b : Nat) : Bool :=
  decide ((a + 2 ^ 255) % WORD_MOD ≤ (b + 2 ^ 255) % WORD_MOD)

/-- One comparison per clz seam: `f(2^t) ≥ f(2^t - 1)` for `t ∈ [1, 254]`. -/
def seamMono (f : Nat → Nat) : Bool :=
  (List.range 254).all fun t => sle (f (2 ^ (t + 1) - 1)) (f (2 ^ (t + 1)))

/-- `lnWad(10**18) = 0` exactly (the branchless `eq` correction in the
implementation lands the lone integer-valued point of the function). -/
theorem model_ln_wad_one_wad : model_ln_wad_evm (10 ^ 18) = 0 := by decide

/-- `lnWadToWad(10**18) = 0` exactly. -/
theorem model_ln_wad_to_wad_one_wad : model_ln_wad_to_wad_evm (10 ^ 18) = 0 := by
  decide

/-- The `x = 10**18` correction preserves order against both neighbors. -/
theorem model_ln_wad_one_wad_mono :
    (sle (model_ln_wad_evm (10 ^ 18 - 1)) (model_ln_wad_evm (10 ^ 18))
      && sle (model_ln_wad_evm (10 ^ 18)) (model_ln_wad_evm (10 ^ 18 + 1))) = true := by
  decide

/-- `lnWad` is monotone across every clz seam. -/
theorem model_ln_wad_seam_mono : seamMono model_ln_wad_evm = true := by decide

/-- `lnWadToWad` is monotone across every clz seam. -/
theorem model_ln_wad_to_wad_seam_mono : seamMono model_ln_wad_to_wad_evm = true := by
  decide

end LnGeneratedModel

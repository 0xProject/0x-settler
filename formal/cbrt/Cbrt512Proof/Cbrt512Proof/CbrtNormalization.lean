/-
  Normalization: EVM shift = clz(x_hi)/3, left-shift x by 3*shift.

  For x_hi > 0:
    shift = evmDiv(evmClz(x_hi), 3)
    x_hi_1 = evmOr(evmShl(shift*3, x_hi), evmShr(256 - shift*3, x_lo))
    x_lo_1 = evmShl(shift*3, x_lo)

  Properties:
    (1) x_hi_1 * 2^256 + x_lo_1 = (x_hi * 2^256 + x_lo) * 2^(3*shift)
    (2) 2^253 ≤ x_hi_1 < 2^256
    (3) x_lo_1 < 2^256
    (4) shift < 86 (so 3*shift < 256)
-/
import Cbrt512Proof.GeneratedCbrt512Model

namespace Cbrt512Spec

open Cbrt512GeneratedModel

-- ============================================================================
-- CLZ / shift properties
-- ============================================================================

/-- For x_hi > 0 and x_hi < 2^256, evmClz(x_hi) = 255 - Nat.log2(x_hi). -/
theorem evmClz_of_pos (x_hi : Nat) (hpos : 0 < x_hi) (hlt : x_hi < WORD_MOD) :
    evmClz x_hi = 255 - Nat.log2 x_hi := by
  unfold evmClz u256
  simp [Nat.mod_eq_of_lt hlt, Nat.ne_of_gt hpos]

/-- clz(x_hi) < 256 for x_hi < 2^256. -/
theorem clz_lt_256 (x_hi : Nat) (hpos : 0 < x_hi) (hlt : x_hi < WORD_MOD) :
    evmClz x_hi < 256 := by
  rw [evmClz_of_pos x_hi hpos hlt]
  have hlog : Nat.log2 x_hi < 256 := by
    exact (Nat.log2_lt (Nat.ne_of_gt hpos)).2 (by unfold WORD_MOD at hlt; exact hlt)
  omega

/-- shift = clz(x_hi) / 3 < 86. -/
theorem shift_lt_86 (x_hi : Nat) (hpos : 0 < x_hi) (hlt : x_hi < WORD_MOD) :
    evmClz x_hi / 3 < 86 := by
  have h := clz_lt_256 x_hi hpos hlt
  omega

/-- 3 * shift < 256. -/
theorem three_shift_lt_256 (x_hi : Nat) (hpos : 0 < x_hi) (hlt : x_hi < WORD_MOD) :
    3 * (evmClz x_hi / 3) < 256 := by
  have h := shift_lt_86 x_hi hpos hlt; omega

/-- After normalization, x_hi_1 ≥ 2^253.
    Since clz(x_hi) = 255 - log2(x_hi), shift = (255 - log2(x_hi))/3,
    and 3*shift ≤ 255 - log2(x_hi), the top bit of x after shifting is at least
    log2(x_hi) + 3*shift ≥ log2(x_hi) + 255 - log2(x_hi) - 2 = 253. -/
theorem normalized_x_hi_ge_253 (x_hi x_lo : Nat)
    (hxhi_pos : 0 < x_hi) (hxhi : x_hi < 2 ^ 256) (hxlo : x_lo < 2 ^ 256) :
    let shift := evmClz x_hi / 3
    let s3 := 3 * shift
    let x_hi_1 := (x_hi * 2 ^ s3 + x_lo * 2 ^ s3 / 2 ^ 256) % 2 ^ 256
    2 ^ 253 ≤ x_hi_1 := by
  sorry

/-- After normalization, x_hi_1 < 2^256. -/
theorem normalized_x_hi_lt (x_hi x_lo : Nat)
    (hxhi_pos : 0 < x_hi) (hxhi : x_hi < 2 ^ 256) (hxlo : x_lo < 2 ^ 256) :
    let shift := evmClz x_hi / 3
    let s3 := 3 * shift
    let x_hi_1 := (x_hi * 2 ^ s3 + x_lo * 2 ^ s3 / 2 ^ 256) % 2 ^ 256
    x_hi_1 < 2 ^ 256 := by
  simp only; exact Nat.mod_lt _ (Nat.two_pow_pos 256)

-- ============================================================================
-- EVM normalization bridge
-- ============================================================================

/-- The EVM normalization computes the same values as Nat arithmetic. -/
theorem evm_normalization_correct (x_hi x_lo : Nat)
    (hxhi_pos : 0 < x_hi) (hxhi : x_hi < 2 ^ 256) (hxlo : x_lo < 2 ^ 256) :
    let hxhi_wm : x_hi < WORD_MOD := by unfold WORD_MOD; exact hxhi
    let hxlo_wm : x_lo < WORD_MOD := by unfold WORD_MOD; exact hxlo
    let shift := evmDiv (evmClz x_hi) 3
    let s3 := evmMul shift 3
    let x_lo_1 := evmShl s3 x_lo
    let x_hi_1 := evmOr (evmShl s3 x_hi) (evmShr (evmSub 256 s3) x_lo)
    -- shift is the floor division
    shift = evmClz x_hi / 3 ∧
    -- s3 = 3 * shift (no overflow)
    s3 = 3 * shift ∧
    -- The normalized values reconstruct x * 2^(3*shift) mod 2^512
    x_hi_1 * 2 ^ 256 + x_lo_1 = (x_hi * 2 ^ 256 + x_lo) * 2 ^ (3 * (evmClz x_hi / 3)) % (2 ^ 512) ∧
    -- x_hi_1 ≥ 2^253
    2 ^ 253 ≤ x_hi_1 ∧
    -- EVM bounds
    x_hi_1 < WORD_MOD ∧
    x_lo_1 < WORD_MOD := by
  sorry

end Cbrt512Spec

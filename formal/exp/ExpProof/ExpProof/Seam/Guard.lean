import Common.Word

/-!
# The overflow-guard comparison

`fun_expRayToWad_68` branches on `iszero(slt(x, C))` with `C = 0x92b2f16cc66c5a4ae96e80d4`
(the first input whose octave count reaches 65). For a signed
input `x ≥ C` (with `u256 x < 2^255`, i.e. `x` a nonnegative signed value at least `C`), the
signed comparison `slt(x, C)` is `0`, so the guard `iszero(slt(x, C))` is `1` and the revert
branch is taken. Both `x` and `C` are below `2^255`, so neither is a negative signed value and the
comparison reduces to the unsigned `¬ (u256 x < C)`.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

/-- `C = 0x92b2f16cc66c5a4ae96e80d4` is below `2^255` (it is `≈ 2^95`). -/
theorem thresh_lt_pow : (0x92b2f16cc66c5a4ae96e80d4 : Nat) < 2 ^ 255 := by decide

/-- The overflow guard `slt(x, C)` is the word `0` for a signed input at or above the threshold,
so `iszero(slt(x, C))` is `1` and the revert branch fires. -/
theorem slt_thresh_ge {x : Nat}
    (h1 : (0x92b2f16cc66c5a4ae96e80d4 : Nat) ≤ u256 x) (h2 : u256 x < 2 ^ 255) :
    EvmYul.UInt256.slt (EvmYul.UInt256.ofNat x)
        (EvmYul.UInt256.ofNat 0x92b2f16cc66c5a4ae96e80d4)
      = EvmYul.UInt256.ofNat 0 := by
  have hx : (EvmYul.UInt256.ofNat x).toNat = u256 x := by
    have := wordNat_ofNat x; simpa [wordNat] using this
  have hC : (EvmYul.UInt256.ofNat 0x92b2f16cc66c5a4ae96e80d4).toNat
      = 0x92b2f16cc66c5a4ae96e80d4 := by
    have := wordNat_ofNat 0x92b2f16cc66c5a4ae96e80d4
    simpa [wordNat, u256, WORD_MOD] using this
  have hCb : (0x92b2f16cc66c5a4ae96e80d4 : Nat) < 2 ^ 255 := thresh_lt_pow
  unfold EvmYul.UInt256.slt EvmYul.UInt256.sltBool
  rw [hx, hC]
  rw [if_neg (by omega : ¬ (u256 x ≥ 2 ^ 255))]
  rw [if_neg (by omega : ¬ ((0x92b2f16cc66c5a4ae96e80d4 : Nat) ≥ 2 ^ 255))]
  have hnlt : ¬ EvmYul.UInt256.ofNat x
      < EvmYul.UInt256.ofNat 0x92b2f16cc66c5a4ae96e80d4 := by
    show ¬ (EvmYul.UInt256.ofNat x).toNat
      < (EvmYul.UInt256.ofNat 0x92b2f16cc66c5a4ae96e80d4).toNat
    rw [hx, hC]; omega
  simp [EvmYul.UInt256.fromBool, hnlt]

/-- The overflow guard `slt(x, C)` is the word `1` for a signed input strictly below the threshold
(`x` either a negative signed value, `2^255 ≤ u256 x`, or a nonnegative value below `C`), so
`iszero(slt(x, C))` is `0` and the panic branch is skipped (value path). -/
theorem slt_thresh_lt {x : Nat}
    (hval : u256 x < 0x92b2f16cc66c5a4ae96e80d4 ∨ 2 ^ 255 ≤ u256 x) :
    EvmYul.UInt256.slt (EvmYul.UInt256.ofNat x)
        (EvmYul.UInt256.ofNat 0x92b2f16cc66c5a4ae96e80d4)
      = EvmYul.UInt256.ofNat 1 := by
  have hx : (EvmYul.UInt256.ofNat x).toNat = u256 x := by
    have := wordNat_ofNat x; simpa [wordNat] using this
  have hC : (EvmYul.UInt256.ofNat 0x92b2f16cc66c5a4ae96e80d4).toNat
      = 0x92b2f16cc66c5a4ae96e80d4 := by
    have := wordNat_ofNat 0x92b2f16cc66c5a4ae96e80d4
    simpa [wordNat, u256, WORD_MOD] using this
  have hCb : (0x92b2f16cc66c5a4ae96e80d4 : Nat) < 2 ^ 255 := thresh_lt_pow
  unfold EvmYul.UInt256.slt EvmYul.UInt256.sltBool
  rw [hx, hC]
  rw [if_neg (by omega : ¬ ((0x92b2f16cc66c5a4ae96e80d4 : Nat) ≥ 2 ^ 255))]
  rcases hval with hlt | hneg
  · rw [if_neg (by omega : ¬ (u256 x ≥ 2 ^ 255))]
    have hlt' : EvmYul.UInt256.ofNat x
        < EvmYul.UInt256.ofNat 0x92b2f16cc66c5a4ae96e80d4 := by
      show (EvmYul.UInt256.ofNat x).toNat
        < (EvmYul.UInt256.ofNat 0x92b2f16cc66c5a4ae96e80d4).toNat
      rw [hx, hC]; omega
    simp [EvmYul.UInt256.fromBool, hlt']
  · rw [if_pos (by omega : u256 x ≥ 2 ^ 255)]
    simp [EvmYul.UInt256.fromBool]

end ExpYul

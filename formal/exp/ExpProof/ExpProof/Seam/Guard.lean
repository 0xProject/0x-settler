import ExpProof.Seam.RuntimeShared

/-!
# The overflow-guard comparison

`fun_expRayToWad_70` branches on `iszero(slt(x, C))` with `C = 0x8e383a2cdfa1b74a9422d2e1`
(`= 0x8e383a2cdfa1b74a9422d2e1`, the first input whose octave count reaches 64). For a signed
input `x ≥ C` (with `u256 x < 2^255`, i.e. `x` a nonnegative signed value at least `C`), the
signed comparison `slt(x, C)` is `0`, so the guard `iszero(slt(x, C))` is `1` and the revert
branch is taken. Both `x` and `C` are below `2^255`, so neither is a negative signed value and the
comparison reduces to the unsigned `¬ (u256 x < C)`.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

/-- `C = 0x8e383a2cdfa1b74a9422d2e1` is below `2^255` (it is `≈ 2^95`). -/
theorem thresh_lt_pow : (0x8e383a2cdfa1b74a9422d2e1 : Nat) < 2 ^ 255 := by decide

/-- The overflow guard `slt(x, C)` is the word `0` for a signed input at or above the threshold,
so `iszero(slt(x, C))` is `1` and the revert branch fires. -/
theorem slt_thresh_ge {x : Nat}
    (h1 : (0x8e383a2cdfa1b74a9422d2e1 : Nat) ≤ u256 x) (h2 : u256 x < 2 ^ 255) :
    EvmYul.UInt256.slt (EvmYul.UInt256.ofNat x)
        (EvmYul.UInt256.ofNat 0x8e383a2cdfa1b74a9422d2e1)
      = EvmYul.UInt256.ofNat 0 := by
  have hx : (EvmYul.UInt256.ofNat x).toNat = u256 x := by
    have := wordNat_ofNat x; simpa [wordNat] using this
  have hC : (EvmYul.UInt256.ofNat 0x8e383a2cdfa1b74a9422d2e1).toNat
      = 0x8e383a2cdfa1b74a9422d2e1 := by
    have := wordNat_ofNat 0x8e383a2cdfa1b74a9422d2e1
    simpa [wordNat, u256, WORD_MOD] using this
  have hCb : (0x8e383a2cdfa1b74a9422d2e1 : Nat) < 2 ^ 255 := thresh_lt_pow
  unfold EvmYul.UInt256.slt EvmYul.UInt256.sltBool
  rw [hx, hC]
  rw [if_neg (by omega : ¬ (u256 x ≥ 2 ^ 255))]
  rw [if_neg (by omega : ¬ ((0x8e383a2cdfa1b74a9422d2e1 : Nat) ≥ 2 ^ 255))]
  have hnlt : ¬ EvmYul.UInt256.ofNat x
      < EvmYul.UInt256.ofNat 0x8e383a2cdfa1b74a9422d2e1 := by
    show ¬ (EvmYul.UInt256.ofNat x).toNat
      < (EvmYul.UInt256.ofNat 0x8e383a2cdfa1b74a9422d2e1).toNat
    rw [hx, hC]; omega
  simp [EvmYul.UInt256.fromBool, hnlt]

end ExpYul

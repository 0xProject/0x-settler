import Sqrt512Proof.Sqrt512YulProof
import Sqrt512Proof.Sqrt512Correct
import Sqrt512Proof.SqrtUpCorrect

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 1024
set_option linter.style.nameCheck false

namespace Sqrt512Yul

open FormalYul

private theorem uint512_lt_512 (xHi xLo : Nat) :
    uint512 xHi xLo < 2 ^ 512 := by
  have hxHi : FormalYul.u256 xHi < 2 ^ 256 := by
    unfold FormalYul.u256 FormalYul.WORD_MOD
    exact Nat.mod_lt xHi (Nat.two_pow_pos 256)
  have hxLo : FormalYul.u256 xLo < 2 ^ 256 := by
    unfold FormalYul.u256 FormalYul.WORD_MOD
    exact Nat.mod_lt xLo (Nat.two_pow_pos 256)
  unfold uint512
  have hmul : FormalYul.u256 xHi * 2 ^ 256 < 2 ^ 256 * 2 ^ 256 :=
    Nat.mul_lt_mul_of_pos_right hxHi (Nat.two_pow_pos 256)
  have hpow : (2 : Nat) ^ 256 * 2 ^ 256 = 2 ^ 512 := by
    rw [← Nat.pow_add]
  omega

theorem sqrt512_uint512_eq_natSqrt (xHi xLo : Nat) :
    sqrt512 (uint512 xHi xLo) = natSqrt (uint512 xHi xLo) := by
  exact sqrt512_correct (uint512 xHi xLo) (uint512_lt_512 xHi xLo)

private theorem natSqrt_uint512_lt_word (xHi xLo : Nat) :
    natSqrt (uint512 xHi xLo) < FormalYul.WORD_MOD := by
  rw [FormalYul.WORD_MOD]
  by_contra hnot
  have hle : 2 ^ 256 ≤ natSqrt (uint512 xHi xLo) := Nat.le_of_not_gt hnot
  have hsquare := natSqrt_sq_le (uint512 xHi xLo)
  have hge : 2 ^ 512 ≤ uint512 xHi xLo := by
    calc
      2 ^ 512 = 2 ^ 256 * 2 ^ 256 := by rw [← Nat.pow_add]
      _ ≤ natSqrt (uint512 xHi xLo) * natSqrt (uint512 xHi xLo) :=
        Nat.mul_le_mul hle hle
      _ ≤ uint512 xHi xLo := hsquare
  exact not_le_of_gt (uint512_lt_512 xHi xLo) hge

private theorem sqrtUp512_uint512_le_word (xHi xLo : Nat) :
    sqrtUp512 (uint512 xHi xLo) ≤ 2 ^ 256 := by
  have hcorrect := sqrtUp512_correct (uint512 xHi xLo) (uint512_lt_512 xHi xLo)
  exact hcorrect.2 (2 ^ 256) (by
    have hx : uint512 xHi xLo < 2 ^ 512 := uint512_lt_512 xHi xLo
    have hpow : (2 : Nat) ^ 256 * 2 ^ 256 = 2 ^ 512 := by
      rw [← Nat.pow_add]
    omega)

private theorem sqrtUp512Pair_u256_components (xHi xLo : Nat) :
    (FormalYul.u256 (sqrtUp512Pair xHi xLo).1,
      FormalYul.u256 (sqrtUp512Pair xHi xLo).2) =
      sqrtUp512Pair xHi xLo := by
  unfold sqrtUp512Pair
  let r := sqrtUp512 (uint512 xHi xLo)
  have hr : r ≤ 2 ^ 256 := by
    simpa [r] using sqrtUp512_uint512_le_word xHi xLo
  have hhi : r / 2 ^ 256 < FormalYul.WORD_MOD := by
    rw [FormalYul.WORD_MOD]
    have hle : r / 2 ^ 256 ≤ 1 := by
      exact Nat.div_le_of_le_mul (by simpa using hr)
    omega
  have hlo : r % 2 ^ 256 < FormalYul.WORD_MOD := by
    rw [FormalYul.WORD_MOD]
    exact Nat.mod_lt r (Nat.two_pow_pos 256)
  change
    (FormalYul.u256 (r / 2 ^ 256), FormalYul.u256 (r % 2 ^ 256)) =
      (r / 2 ^ 256, r % 2 ^ 256)
  apply Prod.ext
  · exact FormalYul.u256_eq_self_of_lt hhi
  · exact FormalYul.u256_eq_self_of_lt hlo

end Sqrt512Yul

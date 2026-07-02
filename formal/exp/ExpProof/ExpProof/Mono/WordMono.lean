import Common.Word

/-!
# Word-level monotonicity and transport lemmas for the `exp` tree

The `exp` monotonicity argument reasons about `<TREE x>` (an `evm*` Nat expression) through its
two's-complement signed view `int256`. This file collects the contract-agnostic facts the
argument needs that the shared `FormalYul.Preservation` does not already provide:

* the in-range `evmDiv` evaluations (plain `Nat` division) and the `evmSar`/`evmDiv` word bounds;
* small `Int` multiplication-monotonicity helpers.

`FormalYul.Preservation` supplies the `int256` transports for `add`/`sub`/`mul` and the
`int256`/`uint256OfInt` round-trips, and `Common.Word` supplies the general shift/division floor
lemmas; both are re-exported under the short names the tree lemmas use.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation
open Common.Word

set_option maxRecDepth 100000

/-! ## Power numerals as `Int` (for `omega`) -/

theorem ipow256 :
    (2 : Int) ^ 256 =
      115792089237316195423570985008687907853269984665640564039457584007913129639936 :=
  intPow256

theorem ipow255 :
    (2 : Int) ^ 255 =
      57896044618658097711785492504343953926634992332820282019728792003956564819968 :=
  intPow255

/-! ## `Int` multiplication-monotonicity helpers -/

theorem mul_le_mul_right_nonneg {a b c : Int} (h : a ≤ b) (hc : 0 ≤ c) : a * c ≤ b * c :=
  Int.mul_le_mul_of_nonneg_right h hc

theorem mul_le_mul_left_nonneg {a b c : Int} (h : a ≤ b) (hc : 0 ≤ c) : c * a ≤ c * b :=
  Int.mul_le_mul_of_nonneg_left h hc

/-! ## Magnitude bounds and the signed-`u256` conversions -/

theorem u256_of_lt {w : Nat} (h : w < 2 ^ 256) : u256 w = w := u256_of_lt_pow256 h

theorem toInt_lt {w : Nat} (h : w < 2 ^ 256) : int256 w < 2 ^ 255 := int256_lt h
theorem toInt_ge {w : Nat} (h : w < 2 ^ 256) : -(2 ^ 255) ≤ int256 w := int256_ge h
theorem toInt_of_lt {w : Nat} (h : w < 2 ^ 255) : int256 w = (w : Int) := int256_of_lt h
theorem ofInt_lt (x : Int) : uint256OfInt x < 2 ^ 256 := uint256OfInt_lt x
theorem toInt_ofInt {x : Int} (h1 : -(2 ^ 255) ≤ x) (h2 : x < 2 ^ 255) :
    int256 (uint256OfInt x) = x := int256_uint256OfInt h1 h2

theorem evmAdd_lt (a b : Nat) : evmAdd a b < 2 ^ 256 := evmAdd_lt_pow256 a b
theorem evmSub_lt (a b : Nat) : evmSub a b < 2 ^ 256 := evmSub_lt_pow256 a b
theorem evmMul_lt (a b : Nat) : evmMul a b < 2 ^ 256 := evmMul_lt_pow256 a b

theorem pow256_pos : (0 : Nat) < 2 ^ 256 := Nat.two_pow_pos 256

theorem evmShr_lt (s w : Nat) : evmShr s w < 2 ^ 256 := Common.Word.evmShr_lt s w

theorem evmShl_lt (s w : Nat) : evmShl s w < 2 ^ 256 := Common.Word.evmShl_lt s w

theorem evmSar_lt (s w : Nat) : evmSar s w < 2 ^ 256 := by
  unfold evmSar u256
  simp only [word_mod_eq]
  have hv : w % 2 ^ 256 < 2 ^ 256 := Nat.mod_lt _ pow256_pos
  have hsub : ∀ X : Nat, 2 ^ 256 - 1 - X < 2 ^ 256 := fun X =>
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) (by omega)
  have hsub1 : (2 ^ 256 - 1 : Nat) < 2 ^ 256 := by omega
  have hdiv : w % 2 ^ 256 / 2 ^ (s % 2 ^ 256) < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hv
  repeat' split
  · exact hsub1
  · exact hsub _
  · exact pow256_pos
  · exact hdiv

theorem evmDiv_lt (a b : Nat) : evmDiv a b < 2 ^ 256 := by
  unfold evmDiv u256
  simp only [word_mod_eq]
  have ha : a % 2 ^ 256 < 2 ^ 256 := Nat.mod_lt _ pow256_pos
  split
  · exact pow256_pos
  · exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha

/-- `evmDiv` on canonical words with a nonzero divisor is plain `Nat` floor division. -/
theorem evmDiv_eq {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) (hb0 : b ≠ 0) :
    evmDiv a b = a / b := by
  unfold evmDiv u256
  simp only [word_mod_eq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  rw [if_neg hb0]

/-- `evmDiv` against the signed view, for a nonnegative dividend and positive divisor: the signed
quotient is the `Nat` floor division of the `Int.toNat` magnitudes. -/
theorem evmDiv_pos_pos {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h1 : 0 ≤ int256 a) (h2 : 0 < int256 b) :
    int256 (evmDiv a b) = (((int256 a).toNat / (int256 b).toNat : Nat) : Int) := by
  have hb0 : ¬ b = 0 := by
    unfold int256 at h2; split at h2 <;> omega
  have hna : ¬ 2 ^ 255 ≤ a := by
    unfold int256 at h1; simp only [ipow256] at *; split at h1 <;> omega
  have hnb : ¬ 2 ^ 255 ≤ b := by
    unfold int256 at h2; simp only [ipow256] at *; split at h2 <;> omega
  have ea : (int256 a).toNat = a := by
    unfold int256; simp only [ipow256] at *; split <;> omega
  have eb : (int256 b).toNat = b := by
    unfold int256; simp only [ipow256] at *; split <;> omega
  rw [evmDiv_eq ha hb hb0, ea, eb]
  have hq : a / b < 2 ^ 255 := by
    have := Nat.div_le_self a b
    omega
  rw [int256_of_lt hq]

/-! ## Re-export of the `add`/`sub`/`mul` transports under short names -/

theorem evmAdd_transport {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h1 : -(2 ^ 255) ≤ int256 a + int256 b) (h2 : int256 a + int256 b < 2 ^ 255) :
    int256 (evmAdd a b) = int256 a + int256 b := evmAdd_int256 ha hb h1 h2

theorem evmSub_transport {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h1 : -(2 ^ 255) ≤ int256 a - int256 b) (h2 : int256 a - int256 b < 2 ^ 255) :
    int256 (evmSub a b) = int256 a - int256 b := evmSub_int256 ha hb h1 h2

theorem evmMul_transport {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h1 : -(2 ^ 255) ≤ int256 a * int256 b) (h2 : int256 a * int256 b < 2 ^ 255) :
    int256 (evmMul a b) = int256 a * int256 b := evmMul_int256 ha hb h1 h2

/-! ## Re-exports of the shared shift/division floor lemmas -/

theorem evmShr_eq_div {s : Nat} (hs : s < 256) {w : Nat} (h : w < 2 ^ 256) :
    evmShr s w = w / 2 ^ s := Common.Word.evmShr_eq_div hs h

theorem evmShl_eq {s : Nat} (hs : s < 256) {w : Nat} (h : w * 2 ^ s < 2 ^ 256) :
    evmShl s w = w * 2 ^ s := Common.Word.evmShl_eq hs h

/-- `evmSar s w` is the signed floor of `int256 w / 2^s` for a shift `s < 256`. The
reduced-argument and `t·Od` shifts are the remaining arithmetic-shift sites. -/
theorem evmSar_sandwich {s : Nat} (hs : s < 256) {w : Nat} (h : w < 2 ^ 256) :
    evmSar s w < 2 ^ 256 ∧
      (2 ^ s : Int) * int256 (evmSar s w) ≤ int256 w ∧
      int256 w < (2 ^ s : Int) * int256 (evmSar s w) + (2 ^ s : Int) :=
  Common.Word.evmSar_sandwich hs h

/-- Cross-multiplication to truncated-division monotonicity over signed positive numerators. -/
theorem cross_to_div {n1 n2 W1 W2 : Int} (hn1 : 0 ≤ n1) (hn2 : 0 ≤ n2)
    (hW1 : 0 < W1) (hW2 : 0 < W2) (hcross : n1 * W2 ≤ n2 * W1) :
    n1.toNat / W1.toNat ≤ n2.toNat / W2.toNat :=
  Common.Word.cross_to_div hn1 hn2 hW1 hW2 hcross

end ExpYul

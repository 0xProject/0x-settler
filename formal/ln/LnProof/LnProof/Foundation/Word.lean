import FormalYul.Preservation

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 10000

/-!
# Two's-complement transport lemmas

`int256` is the signed view of a uint256 word; each lemma here transports one
EVM word opcode to plain `Int` arithmetic under explicit range hypotheses
(no overflow, divisor nonzero, ...). Everything downstream reasons in `Int`.
-/

namespace LnYul

/-- `omega` needs numeral divisors for `Int.emod`; these rewrite the powers. -/
theorem ipow256 :
    (2 : Int) ^ 256 =
      115792089237316195423570985008687907853269984665640564039457584007913129639936 :=
  intPow256

theorem ipow255 :
    (2 : Int) ^ 255 =
      57896044618658097711785492504343953926634992332820282019728792003956564819968 :=
  intPow255

theorem word_mod_eq : WORD_MOD = 2 ^ 256 := rfl

theorem u256_eq (w : Nat) : u256 w = w % 2 ^ 256 := rfl

theorem u256_of_lt {w : Nat} (h : w < 2 ^ 256) : u256 w = w := u256_of_lt_pow256 h

theorem toInt_lt {w : Nat} (h : w < 2 ^ 256) : int256 w < 2 ^ 255 := int256_lt h

theorem toInt_ge {w : Nat} (h : w < 2 ^ 256) : -(2 ^ 255) ≤ int256 w := int256_ge h

theorem toInt_of_lt {w : Nat} (h : w < 2 ^ 255) : int256 w = (w : Int) := int256_of_lt h

theorem ofInt_lt (x : Int) : uint256OfInt x < 2 ^ 256 := uint256OfInt_lt x

theorem toInt_ofInt {x : Int} (h1 : -(2 ^ 255) ≤ x) (h2 : x < 2 ^ 255) :
    int256 (uint256OfInt x) = x := int256_uint256OfInt h1 h2

theorem ofInt_toInt {w : Nat} (h : w < 2 ^ 256) : uint256OfInt (int256 w) = w := by
  unfold int256 uint256OfInt
  simp only [ipow256] at *
  split <;> omega

/-- `sle` (the comparison used by the seam theorems) agrees with `Int`
ordering of the signed views. -/
def sleInt (a b : Nat) : Bool :=
  decide ((a + 2 ^ 255) % WORD_MOD ≤ (b + 2 ^ 255) % WORD_MOD)

theorem sleInt_iff {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) :
    sleInt a b = true ↔ int256 a ≤ int256 b := by
  unfold sleInt int256
  simp only [word_mod_eq, decide_eq_true_eq, ipow256]
  split <;> split <;> omega

/-! ## Opcode transports -/

/-- Master wrap lemma: a Nat congruent to `x` mod `2^256` decodes to `x` when
`x` is in signed range. -/
theorem toInt_wrap {n : Nat} {x : Int}
    (key : (n : Int) % (2 ^ 256 : Int) = x % (2 ^ 256 : Int))
    (h1 : -(2 ^ 255) ≤ x) (h2 : x < 2 ^ 255) :
    int256 (n % 2 ^ 256) = x := by
  unfold int256
  simp only [ipow255, ipow256] at *
  split <;> omega

theorem toInt_mod_cong {w : Nat} (_h : w < 2 ^ 256) :
    (w : Int) % (2 ^ 256 : Int) = int256 w % (2 ^ 256 : Int) := by
  unfold int256
  simp only [ipow256] at *
  split <;> omega

theorem evmAdd_eq (a b : Nat) : evmAdd a b = (a + b) % 2 ^ 256 := by
  unfold evmAdd u256; simp only [word_mod_eq]; omega

theorem evmSub_eq {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) :
    evmSub a b = (a + 2 ^ 256 - b) % 2 ^ 256 := by
  unfold evmSub u256; simp only [word_mod_eq]
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem evmMul_eq {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) :
    evmMul a b = (a * b) % 2 ^ 256 := by
  unfold evmMul u256; simp only [word_mod_eq]
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem evmAdd_lt (a b : Nat) : evmAdd a b < 2 ^ 256 := evmAdd_lt_pow256 a b

theorem evmSub_lt (a b : Nat) : evmSub a b < 2 ^ 256 := evmSub_lt_pow256 a b

theorem evmMul_lt (a b : Nat) : evmMul a b < 2 ^ 256 := evmMul_lt_pow256 a b

theorem evmAdd_transport {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h1 : -(2 ^ 255) ≤ int256 a + int256 b) (h2 : int256 a + int256 b < 2 ^ 255) :
    int256 (evmAdd a b) = int256 a + int256 b := evmAdd_int256 ha hb h1 h2

theorem evmSub_transport {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h1 : -(2 ^ 255) ≤ int256 a - int256 b) (h2 : int256 a - int256 b < 2 ^ 255) :
    int256 (evmSub a b) = int256 a - int256 b := evmSub_int256 ha hb h1 h2

theorem evmMul_transport {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h1 : -(2 ^ 255) ≤ int256 a * int256 b) (h2 : int256 a * int256 b < 2 ^ 255) :
    int256 (evmMul a b) = int256 a * int256 b := evmMul_int256 ha hb h1 h2

end LnYul

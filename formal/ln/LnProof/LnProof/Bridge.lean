import LnProof.LnYulPrimitives

set_option maxRecDepth 10000

/-!
# Two's-complement transport lemmas

`toInt` is the signed view of a uint256 word; each lemma here transports one
EVM word opcode to plain `Int` arithmetic under explicit range hypotheses
(no overflow, divisor nonzero, ...). Everything downstream reasons in `Int`.
-/

namespace LnYul

/-- `omega` needs numeral divisors for `Int.emod`; these rewrite the powers. -/
theorem ipow256 :
    (2 : Int) ^ 256 =
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
  rfl

theorem ipow255 :
    (2 : Int) ^ 255 =
      57896044618658097711785492504343953926634992332820282019728792003956564819968 := by
  rfl

theorem word_mod_eq : WORD_MOD = 2 ^ 256 := rfl

theorem u256_eq (w : Nat) : u256 w = w % 2 ^ 256 := rfl

theorem u256_of_lt {w : Nat} (h : w < 2 ^ 256) : u256 w = w := by
  simpa [u256_eq] using Nat.mod_eq_of_lt h

theorem toInt_lt {w : Nat} (h : w < 2 ^ 256) : toInt w < 2 ^ 255 := by
  unfold toInt; simp only [ipow255, ipow256]; split <;> omega

theorem toInt_ge {w : Nat} (h : w < 2 ^ 256) : -(2 ^ 255) ≤ toInt w := by
  unfold toInt; simp only [ipow255, ipow256]; split <;> omega

theorem toInt_of_lt {w : Nat} (h : w < 2 ^ 255) : toInt w = (w : Int) := by
  unfold toInt; split <;> omega

theorem ofInt_lt (x : Int) : ofInt x < 2 ^ 256 := by
  unfold ofInt; simp only [ipow256]; omega

theorem toInt_ofInt {x : Int} (h1 : -(2 ^ 255) ≤ x) (h2 : x < 2 ^ 255) :
    toInt (ofInt x) = x := by
  unfold toInt ofInt
  simp only [ipow255, ipow256] at *
  split <;> omega

theorem ofInt_toInt {w : Nat} (h : w < 2 ^ 256) : ofInt (toInt w) = w := by
  unfold toInt ofInt
  simp only [ipow256] at *
  split <;> omega

/-- `sle` (the comparison used by the seam theorems) agrees with `Int`
ordering of the signed views. -/
def sleInt (a b : Nat) : Bool :=
  decide ((a + 2 ^ 255) % WORD_MOD ≤ (b + 2 ^ 255) % WORD_MOD)

theorem sleInt_iff {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) :
    sleInt a b = true ↔ toInt a ≤ toInt b := by
  unfold sleInt toInt
  simp only [word_mod_eq, decide_eq_true_eq, ipow256]
  split <;> split <;> omega

/-! ## Opcode transports -/

/-- Master wrap lemma: a Nat congruent to `x` mod `2^256` decodes to `x` when
`x` is in signed range. -/
theorem toInt_wrap {n : Nat} {x : Int}
    (key : (n : Int) % (2 ^ 256 : Int) = x % (2 ^ 256 : Int))
    (h1 : -(2 ^ 255) ≤ x) (h2 : x < 2 ^ 255) :
    toInt (n % 2 ^ 256) = x := by
  unfold toInt
  simp only [ipow255, ipow256] at *
  split <;> omega

theorem toInt_mod_cong {w : Nat} (_h : w < 2 ^ 256) :
    (w : Int) % (2 ^ 256 : Int) = toInt w % (2 ^ 256 : Int) := by
  unfold toInt
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

theorem evmAdd_lt (a b : Nat) : evmAdd a b < 2 ^ 256 := by
  unfold evmAdd u256; simp only [word_mod_eq]; omega

theorem evmSub_lt (a b : Nat) : evmSub a b < 2 ^ 256 := by
  unfold evmSub u256; simp only [word_mod_eq]; omega

theorem evmMul_lt (a b : Nat) : evmMul a b < 2 ^ 256 := by
  unfold evmMul u256; simp only [word_mod_eq]; omega

theorem evmAdd_transport {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h1 : -(2 ^ 255) ≤ toInt a + toInt b) (h2 : toInt a + toInt b < 2 ^ 255) :
    toInt (evmAdd a b) = toInt a + toInt b := by
  rw [evmAdd_eq a b]
  refine toInt_wrap ?_ h1 h2
  have hc : ((a + b : Nat) : Int) = (a : Int) + (b : Int) := by omega
  rw [hc, Int.add_emod, toInt_mod_cong ha, toInt_mod_cong hb, ← Int.add_emod]

theorem evmSub_transport {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h1 : -(2 ^ 255) ≤ toInt a - toInt b) (h2 : toInt a - toInt b < 2 ^ 255) :
    toInt (evmSub a b) = toInt a - toInt b := by
  rw [evmSub_eq ha hb]
  refine toInt_wrap ?_ h1 h2
  have hc : ((a + 2 ^ 256 - b : Nat) : Int) = (a : Int) - (b : Int) + 2 ^ 256 := by
    simp only [ipow256]; omega
  rw [hc, Int.add_emod_right, Int.sub_emod, toInt_mod_cong ha, toInt_mod_cong hb,
    ← Int.sub_emod]

theorem evmMul_transport {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h1 : -(2 ^ 255) ≤ toInt a * toInt b) (h2 : toInt a * toInt b < 2 ^ 255) :
    toInt (evmMul a b) = toInt a * toInt b := by
  rw [evmMul_eq ha hb]
  refine toInt_wrap ?_ h1 h2
  have hc : ((a * b : Nat) : Int) = (a : Int) * (b : Int) := by exact_mod_cast rfl
  rw [hc, Int.mul_emod, toInt_mod_cong ha, toInt_mod_cong hb, ← Int.mul_emod]

end LnYul

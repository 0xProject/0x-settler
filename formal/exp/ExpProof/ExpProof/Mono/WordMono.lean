import ExpProof.Seam.RuntimeShared

/-!
# Word-level monotonicity and transport lemmas for the `exp` tree

The `exp` monotonicity argument reasons about `<TREE x>` (an `evm*` Nat expression) through its
two's-complement signed view `int256`. This file collects the contract-agnostic facts the
argument needs that the shared `FormalYul.Preservation` does not already provide:

* general floor sandwiches for `evmSar`/`evmShr` (the arithmetic/logical right shifts), at an
  arbitrary shift amount, expressed against the signed value;
* the `evmSdiv` sign-pinned transports (one per sign pattern, quotients over `Int.toNat`
  magnitudes);
* cross-multiplied monotonicity of truncated division;
* small `Int` multiplication-monotonicity helpers.

`FormalYul.Preservation` already supplies the `int256` transports for `add`/`sub`/`mul` and the
`int256`/`uint256OfInt` round-trips, so those are used directly.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

/-! ## Power numerals as `Int` (for `omega`) -/

theorem ipow256 :
    (2 : Int) ^ 256 =
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
  norm_num

theorem ipow255 :
    (2 : Int) ^ 255 =
      57896044618658097711785492504343953926634992332820282019728792003956564819968 := by
  norm_num

/-! ## `Int` multiplication-monotonicity helpers -/

theorem mul_le_mul_right_nonneg {a b c : Int} (h : a ≤ b) (hc : 0 ≤ c) : a * c ≤ b * c :=
  Int.mul_le_mul_of_nonneg_right h hc

theorem mul_le_mul_left_nonneg {a b c : Int} (h : a ≤ b) (hc : 0 ≤ c) : c * a ≤ c * b :=
  Int.mul_le_mul_of_nonneg_left h hc

/-- Cancellation of a positive literal factor. -/
theorem le_of_mul_le_mul_pos {a b c : Int} (h : a * c ≤ b * c) (hc : 0 < c) : a ≤ b := by
  rcases Int.lt_or_le b a with hlt | hle
  · exfalso
    have := Int.mul_lt_mul_of_pos_right hlt hc
    omega
  · exact hle

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

theorem evmShr_lt (s w : Nat) : evmShr s w < 2 ^ 256 := by
  unfold evmShr u256
  simp only [word_mod_eq]
  have hv : w % 2 ^ 256 < 2 ^ 256 := Nat.mod_lt _ pow256_pos
  split
  · exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hv
  · exact pow256_pos

theorem evmShl_lt (s w : Nat) : evmShl s w < 2 ^ 256 := by
  unfold evmShl u256
  simp only [word_mod_eq]
  split
  · exact Nat.mod_lt _ pow256_pos
  · exact pow256_pos

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

theorem evmSdiv_lt (a b : Nat) : evmSdiv a b < 2 ^ 256 := by
  unfold evmSdiv u256
  simp only [word_mod_eq]
  have ha : a % 2 ^ 256 < 2 ^ 256 := Nat.mod_lt _ pow256_pos
  have hb : b % 2 ^ 256 < 2 ^ 256 := Nat.mod_lt _ pow256_pos
  repeat' split
  all_goals (first | exact Nat.mod_lt _ pow256_pos | omega)

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

/-! ## `evmShr` as floor division for in-range nonnegative operands -/

theorem evmShr_eq_div {s : Nat} (hs : s < 256) {w : Nat} (h : w < 2 ^ 256) :
    evmShr s w = w / 2 ^ s := by
  have hwm : w % 2 ^ 256 = w := Nat.mod_eq_of_lt h
  have hsm : s % 2 ^ 256 = s := Nat.mod_eq_of_lt (by omega)
  unfold evmShr u256
  simp only [word_mod_eq, hwm, hsm]
  rw [if_pos (by omega : s < 256)]

/-! ## `evmShl` as multiplication when the product fits -/

theorem evmShl_eq {s : Nat} (hs : s < 256) {w : Nat} (h : w * 2 ^ s < 2 ^ 256) :
    evmShl s w = w * 2 ^ s := by
  unfold evmShl u256
  simp only [word_mod_eq]
  have hs2 : s % 2 ^ 256 = s := Nat.mod_eq_of_lt (by omega)
  have hpos : 0 < 2 ^ s := Nat.two_pow_pos s
  have hw : w < 2 ^ 256 := by
    have h1 : w * 1 ≤ w * 2 ^ s := Nat.mul_le_mul_left w hpos
    omega
  rw [hs2, if_pos hs, Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt h]

/-! ## `evmSar` general floor sandwich (signed value) -/

/-- `evmSar s w` is the signed floor of `int256 w / 2^s` for a shift `s < 256`:
`2^s · int256 (evmSar s w) ≤ int256 w < 2^s · int256 (evmSar s w) + 2^s`, and the result is a
valid word. This is the single fact the floor step needs (`s = 126 - k` is a runtime value, and
`126 - k ∈ [63, 127]` over the supported octaves). -/
theorem evmSar_sandwich {s : Nat} (hs : s < 256) {w : Nat} (h : w < 2 ^ 256) :
    evmSar s w < 2 ^ 256 ∧
      (2 ^ s : Int) * int256 (evmSar s w) ≤ int256 w ∧
      int256 w < (2 ^ s : Int) * int256 (evmSar s w) + (2 ^ s : Int) := by
  have hps : (0 : Nat) < 2 ^ s := Nat.two_pow_pos s
  have hwm : w % 2 ^ 256 = w := Nat.mod_eq_of_lt h
  have hsm : s % 2 ^ 256 = s := Nat.mod_eq_of_lt (by omega)
  -- `2^256 = 2^s * 2^(256-s)`, so the complement's floor relates to `w`'s floor.
  have hsplit : (2 : Nat) ^ 256 = 2 ^ s * 2 ^ (256 - s) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hsne : ¬ 256 ≤ s := by omega
  unfold evmSar u256 int256
  simp only [word_mod_eq, hwm, hsm, hsne, if_false]
  by_cases hneg : 2 ^ 255 ≤ w
  · rw [if_pos hneg]
    -- result word = 2^256 - 1 - (2^256 - 1 - w)/2^s; it is in the negative half.
    set m := 2 ^ 256 - 1 - w with hm
    set q := m / 2 ^ s with hq
    have hmlt : m < 2 ^ 255 := by omega
    -- floor facts for q
    have hqlo : 2 ^ s * q ≤ m := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self m (2 ^ s)
    have hqhi : m < 2 ^ s * q + 2 ^ s := by
      have hdm := Nat.div_add_mod m (2 ^ s)
      have hmod := Nat.mod_lt m hps
      have hc : 2 ^ s * (m / 2 ^ s) = q * 2 ^ s := by rw [← hq]; exact Nat.mul_comm _ _
      have hc2 : 2 ^ s * q = q * 2 ^ s := Nat.mul_comm _ _
      omega
    have hqle : q ≤ m := by rw [hq]; exact Nat.div_le_self m (2 ^ s)
    have hqlt : q < 2 ^ 255 := by omega
    -- the result word `rw = 2^256 - 1 - q` lies in the negative half
    have hrwlt : (2 ^ 256 - 1 - q) < 2 ^ 256 :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) (by omega)
    have hrwneg : 2 ^ 255 ≤ 2 ^ 256 - 1 - q := by omega
    rw [if_neg (Nat.not_lt.mpr hrwneg)]
    rw [if_neg (Nat.not_lt.mpr hneg)]
    -- Cast the Nat-level floor facts to `Int` once, as relations among `↑q`, `↑w`, `↑(2^s)`.
    have hqloI : (2 ^ s : Int) * (q : Int) ≤ (2 ^ 256 : Int) - 1 - (w : Int) := by
      have h0 : ((2 ^ s * q : Nat) : Int) ≤ ((m : Nat) : Int) := by exact_mod_cast hqlo
      have hmI : ((m : Nat) : Int) = (2 ^ 256 : Int) - 1 - (w : Int) := by
        rw [hm]; simp only [ipow256]; push_cast [Nat.sub_sub]; omega
      push_cast at h0; rw [hmI] at h0; linarith
    have hqhiI : (2 ^ 256 : Int) - 1 - (w : Int) < (2 ^ s : Int) * (q : Int) + (2 ^ s : Int) := by
      have h0 : ((m : Nat) : Int) < ((2 ^ s * q + 2 ^ s : Nat) : Int) := by exact_mod_cast hqhi
      have hmI : ((m : Nat) : Int) = (2 ^ 256 : Int) - 1 - (w : Int) := by
        rw [hm]; simp only [ipow256]; push_cast [Nat.sub_sub]; omega
      push_cast at h0; rw [hmI] at h0; linarith
    have hresI : ((2 ^ 256 - 1 - q : Nat) : Int) = (2 ^ 256 : Int) - 1 - (q : Int) := by
      simp only [ipow256]; push_cast [Nat.sub_sub]; omega
    refine ⟨hrwlt, ?_, ?_⟩
    · rw [hresI]; nlinarith [hqloI]
    · rw [hresI]; nlinarith [hqhiI]
  · rw [if_neg hneg]
    -- nonnegative: result word = w / 2^s, both halves nonnegative.
    set q := w / 2 ^ s with hq
    have hqlt : q < 2 ^ 255 := by
      have : w / 2 ^ s ≤ w := Nat.div_le_self w (2 ^ s)
      omega
    have hqlt2 : q < 2 ^ 256 := by omega
    rw [if_pos hqlt, if_pos (by omega : w < 2 ^ 255)]
    have hfloor := Nat.div_mul_le_self w (2 ^ s)
    have hfloor2 : w < (w / 2 ^ s) * 2 ^ s + 2 ^ s := by
      have hdm := Nat.div_add_mod w (2 ^ s)
      have hmod := Nat.mod_lt w hps
      have hc : 2 ^ s * (w / 2 ^ s) = (w / 2 ^ s) * 2 ^ s := Nat.mul_comm _ _
      omega
    refine ⟨hqlt2, ?_, ?_⟩
    · have he : (2 ^ s : Int) * (q : Int) = ((2 ^ s * q : Nat) : Int) := by push_cast; ring
      rw [he]
      have hh : 2 ^ s * q ≤ w := by rw [hq, Nat.mul_comm]; exact hfloor
      exact_mod_cast hh
    · have he : (2 ^ s : Int) * (q : Int) + (2 ^ s : Int) = ((2 ^ s * q + 2 ^ s : Nat) : Int) := by
        push_cast; ring
      rw [he]
      have hh : w < 2 ^ s * q + 2 ^ s := by rw [hq, Nat.mul_comm]; exact hfloor2
      exact_mod_cast hh

/-! ## `evmSdiv` sign-pinned transports -/

theorem toInt_u256_of_small {q : Nat} (h : q < 2 ^ 255) : int256 (u256 q) = (q : Int) := by
  unfold int256 u256
  simp only [word_mod_eq, ipow256] at *
  split <;> omega

theorem toInt_u256_neg {q : Nat} (h : q ≤ 2 ^ 255) :
    int256 (u256 (WORD_MOD - q)) = -(q : Int) := by
  unfold int256 u256
  simp only [word_mod_eq, ipow256] at *
  split <;> omega

theorem evmSdiv_pos_pos {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h1 : 0 ≤ int256 a) (h2 : 0 < int256 b) :
    int256 (evmSdiv a b) = (((int256 a).toNat / (int256 b).toNat : Nat) : Int) := by
  have hna : ¬ 2 ^ 255 ≤ a := by
    unfold int256 at h1; simp only [ipow256] at *; split at h1 <;> omega
  have hnb : ¬ 2 ^ 255 ≤ b := by
    unfold int256 at h2; simp only [ipow256] at *; split at h2 <;> omega
  have hb0 : ¬ b = 0 := by
    unfold int256 at h2; split at h2 <;> omega
  have ea : (int256 a).toNat = a := by
    unfold int256; simp only [ipow256] at *; split <;> omega
  have eb : (int256 b).toNat = b := by
    unfold int256; simp only [ipow256] at *; split <;> omega
  unfold evmSdiv
  simp only [u256_of_lt ha, u256_of_lt hb, decide_eq_false hna, decide_eq_false hnb,
    Bool.false_eq_true, if_true, if_false, if_neg hb0, ea, eb]
  have hq : a / b < 2 ^ 255 := by
    have := Nat.div_le_self a b
    omega
  rw [toInt_u256_of_small hq]

theorem evmSdiv_neg_pos {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h1 : int256 a < 0) (hmin : -(2 ^ 255) < int256 a) (h2 : 0 < int256 b) :
    int256 (evmSdiv a b) = -(((- int256 a).toNat / (int256 b).toNat : Nat) : Int) := by
  have hna : 2 ^ 255 ≤ a := by
    unfold int256 at h1; simp only [ipow255, ipow256] at *; split at h1 <;> omega
  have hnb : ¬ 2 ^ 255 ≤ b := by
    unfold int256 at h2; simp only [ipow255, ipow256] at *; split at h2 <;> omega
  have hb0 : ¬ b = 0 := by
    unfold int256 at h2; split at h2 <;> omega
  have ea : (- int256 a).toNat = WORD_MOD - a := by
    unfold int256; simp only [word_mod_eq, ipow255, ipow256] at *; split <;> omega
  have eb : (int256 b).toNat = b := by
    unfold int256; simp only [ipow255, ipow256] at *; split <;> omega
  unfold evmSdiv
  simp only [u256_of_lt ha, u256_of_lt hb, decide_eq_true hna, decide_eq_false hnb,
    Bool.false_eq_true, Bool.true_eq_false, if_true, if_false, if_neg hb0, ea, eb]
  have hq : (WORD_MOD - a) / b ≤ 2 ^ 255 := by
    have h3 : WORD_MOD - a ≤ 2 ^ 255 := by
      unfold int256 at hmin; simp only [word_mod_eq, ipow255, ipow256] at *
      split at hmin <;> omega
    have := Nat.div_le_self (WORD_MOD - a) b
    omega
  rw [toInt_u256_neg hq]

theorem evmSdiv_pos_neg {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h1 : 0 ≤ int256 a) (h2 : int256 b < 0) :
    int256 (evmSdiv a b) = -(((int256 a).toNat / (- int256 b).toNat : Nat) : Int) := by
  have hna : ¬ 2 ^ 255 ≤ a := by
    unfold int256 at h1; simp only [ipow256] at *; split at h1 <;> omega
  have hnb : 2 ^ 255 ≤ b := by
    unfold int256 at h2; simp only [ipow256] at *; split at h2 <;> omega
  have hb0 : ¬ b = 0 := by
    intro h; subst h; simp only [] at hnb; omega
  have ea : (int256 a).toNat = a := by
    unfold int256; simp only [ipow256] at *; split <;> omega
  have eb : (- int256 b).toNat = WORD_MOD - b := by
    unfold int256; simp only [word_mod_eq, ipow256] at *; split <;> omega
  unfold evmSdiv
  simp only [u256_of_lt ha, u256_of_lt hb, decide_eq_false hna, decide_eq_true hnb,
    Bool.false_eq_true, if_true, if_false, if_neg hb0, ea, eb]
  have hq : a / (WORD_MOD - b) ≤ 2 ^ 255 := by
    have h3 : a < 2 ^ 255 := by
      unfold int256 at h1; simp only [ipow256] at *; split at h1 <;> omega
    have := Nat.div_le_self a (WORD_MOD - b)
    omega
  rw [toInt_u256_neg hq]

theorem evmSdiv_neg_neg {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h1 : int256 a < 0) (hmin : -(2 ^ 255) < int256 a) (h2 : int256 b < 0) :
    int256 (evmSdiv a b) = (((- int256 a).toNat / (- int256 b).toNat : Nat) : Int) := by
  have hna : 2 ^ 255 ≤ a := by
    unfold int256 at h1; simp only [ipow255, ipow256] at *; split at h1 <;> omega
  have hnb : 2 ^ 255 ≤ b := by
    unfold int256 at h2; simp only [ipow255, ipow256] at *; split at h2 <;> omega
  have hb0 : ¬ b = 0 := by
    intro h; subst h; simp only [] at hnb; omega
  have ea : (- int256 a).toNat = WORD_MOD - a := by
    unfold int256; simp only [word_mod_eq, ipow255, ipow256] at *; split <;> omega
  have eb : (- int256 b).toNat = WORD_MOD - b := by
    unfold int256; simp only [word_mod_eq, ipow255, ipow256] at *; split <;> omega
  unfold evmSdiv
  simp only [u256_of_lt ha, u256_of_lt hb, decide_eq_true hna, decide_eq_true hnb,
    if_true, if_neg hb0, ea, eb]
  have hq : (WORD_MOD - a) / (WORD_MOD - b) < 2 ^ 255 := by
    have h3 : WORD_MOD - a ≤ 2 ^ 255 := by
      unfold int256 at hmin; simp only [word_mod_eq, ipow255, ipow256] at *
      split at hmin <;> omega
    have := Nat.div_le_self (WORD_MOD - a) (WORD_MOD - b)
    simp only [word_mod_eq, ipow255] at *
    omega
  rw [toInt_u256_of_small hq]

/-! ## Cross-multiplied monotonicity of `Nat` division -/

theorem nat_div_cross_mono {a b c d : Nat} (hb : 0 < b) (hd : 0 < d)
    (h : a * d ≤ c * b) : a / b ≤ c / d := by
  rw [Nat.le_div_iff_mul_le hd]
  have h1 : a / b * b ≤ a := Nat.div_mul_le_self a b
  have h2 : a / b * b * d ≤ a * d := Nat.mul_le_mul_right d h1
  have h3 : a / b * b * d ≤ c * b := Nat.le_trans h2 h
  have h4 : a / b * d * b ≤ c * b := by
    have : a / b * b * d = a / b * d * b := by
      rw [Nat.mul_assoc, Nat.mul_comm b d, ← Nat.mul_assoc]
    omega
  exact Nat.le_of_mul_le_mul_right h4 hb

theorem toNat_mul_of_nonneg {x y : Int} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x.toNat * y.toNat = (x * y).toNat := by
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hx
  obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hy
  rfl

/-- Cross-multiplication to truncated-division monotonicity over signed positive numerators. -/
theorem cross_to_div {n1 n2 W1 W2 : Int} (hn1 : 0 ≤ n1) (hn2 : 0 ≤ n2)
    (hW1 : 0 < W1) (hW2 : 0 < W2) (hcross : n1 * W2 ≤ n2 * W1) :
    n1.toNat / W1.toNat ≤ n2.toNat / W2.toNat := by
  refine nat_div_cross_mono (by omega) (by omega) ?_
  have e1 := toNat_mul_of_nonneg hn1 (by omega : (0:Int) ≤ W2)
  have e2 := toNat_mul_of_nonneg hn2 (by omega : (0:Int) ≤ W1)
  omega

end ExpYul

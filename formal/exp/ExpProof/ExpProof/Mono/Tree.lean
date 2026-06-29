import ExpProof.Mono.WordMono

/-!
# The `exp` tree as a function of the input, in layered pieces

`<TREE x>` (the value `run_exp_ray_to_wad_evm` returns, established by
`run_exp_ray_to_wad_evm_eq_tree`) is captured here, decomposed into thin named layers so that the
deeply-nested Horner accumulator never has to be materialised by the kernel (forcing whnf of the
full tree overflows the C stack — every layer below keeps the next level behind one `def`).

The outermost layer is the zeroing clamp and the scale-point pin:

```
expTree x = evmAdd (evmIszero x) (evmMul (evmSlt C x) (r1Tree x))
```

with `C = ⌊-18·ln10·10²⁷⌋` a negative signed boundary. Monotonicity of `int256 (expTree ·)`
reduces to a single analytic obligation about the floored accumulator `r1Tree` on the meaningful
region `int256 C < int256 x` (the clamp forces `0` below it).
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

/-! ## Constants -/

/-- `C = ⌊-18·ln10·10²⁷⌋`, the greatest `x` whose exact result is below `1` (the 0/1 boundary). -/
def Cmask : Nat := 0xffffffffffffffffffffffffffffffffffffffff7a143b87dbdabf5ee0a0efd7

/-- The supported-range threshold; the run reverts at or above it. -/
def C0thresh : Nat := 0x8e383a2cdfa1b74a9422d2e1

theorem int256_Cmask : int256 Cmask = -41446531673892822312323846185 := by
  unfold Cmask int256
  norm_num

theorem Cmask_lt : Cmask < 2 ^ 256 := by unfold Cmask; norm_num

/-! ## The kernel pieces as thin layered functions of the input word

Each layer is a one-line `def`; the kernel only ever delta-unfolds one level at a time, so the
deep Horner accumulator is never forced into whnf. -/

/-- Octave index word `k = round(x / (10²⁷·ln2))` (half-open, ties toward `+∞`). -/
def kTree (x : Nat) : Nat :=
  evmSar 0xc8 (evmAdd (evmShl 0xc7 1) (evmMul 0x724d54edbacbebbb95c52a0f6076 x))

/-- Reduced argument `t` in Q128. -/
def tTree (x : Nat) : Nat :=
  evmSar 0x6b (evmSub (evmMul 0x279d346de4781f921dd7a89933d54d1f72928 x)
    (evmMul 0x58b90bfbe8e7bcd5e4f1d9cc01f97b57a079a193394c5b16c5068badc5d (kTree x)))

/-- `v = t²` in Q128. -/
def vTree (x : Nat) : Nat := evmShr 0x80 (evmMul (tTree x) (tTree x))

/-- `Ev(v)`, the even (degree-5, monic) Horner accumulator. -/
def evTree (x : Nat) : Nat :=
  let v := vTree x
  evmAdd 0x4e14a45e8ec305e233e11b4174e214ac (evmShr 0x84 (evmMul
    (evmAdd 0x93f11e65781741b92fa7fc4f4fffcca2 (evmShr 0x86 (evmMul
    (evmAdd 0x9064d965e1c4863b73604e0ddbec53f9 (evmShr 0x80 (evmMul
    (evmAdd 0x9a036222e11aee18465042f8ea64c8 (evmShr 0x82 (evmMul
    (evmAdd 0xb9aacfad41060587203a79af0ebc (evmShr 0x1d v)) v))) v))) v))) v))

/-- `Od(v)`, the odd (degree-4) Horner accumulator. -/
def odTree (x : Nat) : Nat :=
  let v := vTree x
  evmAdd 0x270a522f476182f119f08da0ba710a56 (evmShr 0x87 (evmMul
    (evmAdd 0xaf5662483c4ce783a9ef5fe025f42e9e (evmShr 0x7f (evmMul
    (evmAdd 0xad4506b00b1246c7e5b4fd33e1201b (evmShr 0x89 (evmMul
    (evmAdd 0xc926ddbf3830ca5561cc01585402d0 (evmShr 0x83 (evmMul
    0xdc07aff85e5bb5629d0fb64a84bb v))) v))) v))) v))

/-- `t·Od(v)` in Q87 (signed via `t`). -/
def todTree (x : Nat) : Nat := evmSar 0x80 (evmMul (tTree x) (odTree x))

/-- `exp(t)` in Q126: the reciprocal-symmetric quotient `(Ev + t·Od)/(Ev − t·Od)`. -/
def r0Tree (x : Nat) : Nat :=
  evmSdiv (evmShl 0x7e (evmAdd (evTree x) (todTree x))) (evmSub (evTree x) (todTree x))

/-- The floored, `2ᵏ`-scaled, margin-subtracted accumulator (the body upstream of the clamp). -/
def r1Tree (x : Nat) : Nat :=
  evmSar (evmSub 0x7e (kTree x)) (evmSub (evmMul 0xde0b6b3a7640000 (r0Tree x)) 0xafe527e18748a8a)

/-- `<TREE x>`: the clamp/pin shell wrapped around `r1Tree`. -/
def expTree (x : Nat) : Nat :=
  evmAdd (evmIszero x) (evmMul (evmSlt Cmask x) (r1Tree x))

theorem r1Tree_lt (x : Nat) : r1Tree x < 2 ^ 256 := by unfold r1Tree; exact evmSar_lt _ _
theorem expTree_lt (x : Nat) : expTree x < 2 ^ 256 := by unfold expTree; exact evmAdd_lt _ _

/-! ## Small word/`Int` facts for the clamp and pin -/

/-- `evmSlt a b` is the signed comparison (of the canonical words) as a `{0,1}` word. -/
theorem evmSlt_eq_ite (a b : Nat) :
    evmSlt a b = if int256 (u256 a) < int256 (u256 b) then 1 else 0 := by
  have hua : u256 a < 2 ^ 256 := u256_lt_word a
  have hub : u256 b < 2 ^ 256 := u256_lt_word b
  have offneg : ∀ c : Nat, c < 2 ^ 256 → 2 ^ 255 ≤ c →
      (c + 2 ^ 255) % 2 ^ 256 = c - 2 ^ 255 := by
    intro c hc hcn
    rw [show c + 2 ^ 255 = (c - 2 ^ 255) + 2 ^ 256 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  have offpos : ∀ c : Nat, c < 2 ^ 256 → c < 2 ^ 255 →
      (c + 2 ^ 255) % 2 ^ 256 = c + 2 ^ 255 := by
    intro c hc hcp; exact Nat.mod_eq_of_lt (by omega)
  have hai : (u256 a : Int) < 2 ^ 256 := by simp only [ipow256]; exact_mod_cast hua
  have hbi : (u256 b : Int) < 2 ^ 256 := by simp only [ipow256]; exact_mod_cast hub
  -- The offset (excess-2^255) comparison the opcode performs coincides with the signed order.
  have key : ((u256 a + 2 ^ 255) % 2 ^ 256 < (u256 b + 2 ^ 255) % 2 ^ 256) ↔
      (int256 (u256 a) < int256 (u256 b)) := by
    unfold int256
    simp only [ipow255, ipow256] at hai hbi
    by_cases ha : 2 ^ 255 ≤ u256 a <;> by_cases hb : 2 ^ 255 ≤ u256 b
    · rw [offneg _ hua ha, offneg _ hub hb,
        if_neg (by omega : ¬ u256 a < 2 ^ 255), if_neg (by omega : ¬ u256 b < 2 ^ 255)]
      constructor <;> intro h <;> omega
    · rw [offneg _ hua ha, offpos _ hub (by omega),
        if_neg (by omega : ¬ u256 a < 2 ^ 255), if_pos (by omega : u256 b < 2 ^ 255)]
      constructor <;> intro h <;> omega
    · rw [offpos _ hua (by omega), offneg _ hub hb,
        if_pos (by omega : u256 a < 2 ^ 255), if_neg (by omega : ¬ u256 b < 2 ^ 255)]
      constructor <;> intro h <;> omega
    · rw [offpos _ hua (by omega), offpos _ hub (by omega),
        if_pos (by omega : u256 a < 2 ^ 255), if_pos (by omega : u256 b < 2 ^ 255)]
      constructor <;> intro h <;> omega
  have hslt : evmSlt a b = if int256 (u256 a) < int256 (u256 b) then 1 else 0 := by
    unfold evmSlt
    by_cases hcmp : (u256 a + 2 ^ 255) % WORD_MOD < (u256 b + 2 ^ 255) % WORD_MOD
    · have hcmp' : (u256 a + 2 ^ 255) % 2 ^ 256 < (u256 b + 2 ^ 255) % 2 ^ 256 := hcmp
      rw [if_pos hcmp, if_pos (key.mp hcmp')]
    · have hcmp' : ¬ (u256 a + 2 ^ 255) % 2 ^ 256 < (u256 b + 2 ^ 255) % 2 ^ 256 := hcmp
      rw [if_neg hcmp, if_neg (fun h => hcmp' (key.mpr h))]
  exact hslt

/-- `evmIszero x` is `1` exactly when the word is `0`. -/
theorem evmIszero_eq_ite (x : Nat) : evmIszero x = if u256 x = 0 then 1 else 0 := rfl

end ExpYul

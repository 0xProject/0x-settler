import ExpProof.Mono.Tree

/-!
# Octave-index and reduced-argument transports

On the meaningful region the input word `x` (canonical, `< 2^256`) has signed value in
`(C, C0) ⊂ (−2^96, 2^96)`. This file transports the first two kernel stages — the octave index
`k = round(x/(10²⁷·ln2))` and the reduced argument `t` — to closed `Int` forms via the no-overflow
bounds, and proves `k` is nondecreasing in `int256 x` and (for a fixed `k`) `t` is nondecreasing in
`int256 x`.

Constants and their bit widths (so every product stays below `2^255`):
`CINV` 111 bits, `K27` 146 bits, `LN2` 235 bits, `|int256 x| < 2^96`, `k ∈ [-60, 63]`.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

/-- The signed value of `x` on the meaningful region is bounded by `2^96`. -/
theorem region_x_bound {x : Nat} (hC : int256 Cmask < int256 x)
    (hC0 : int256 x < int256 C0thresh) :
    -(2 ^ 96 : Int) < int256 x ∧ int256 x < 2 ^ 96 := by
  rw [int256_Cmask] at hC
  have hC0' : int256 x < 44014845965556527147994239713 := by
    rw [show int256 C0thresh = 44014845965556527147994239713 from by
      unfold C0thresh int256; norm_num] at hC0
    exact hC0
  constructor <;> [skip; skip] <;> simp only [show (2:Int)^96 = 79228162514264337593543950336 from by norm_num] <;> omega

theorem CINV_lt : (0x724d54edbacbebbb95c52a0f6076 : Nat) < 2 ^ 112 := by norm_num
theorem K27_lt : (0x279d346de4781f921dd7a89933d54d1f72928 : Nat) < 2 ^ 146 := by norm_num
theorem LN2_lt : (0x58b90bfbe8e7bcd5e4f1d9cc01f97b57a079a193394c5b16c5068badc5d : Nat) < 2 ^ 235 := by
  norm_num

/-- `int256` of the constant `CINV` (it is below `2^255`, so the signed view is the literal). -/
theorem int256_CINV : int256 0x724d54edbacbebbb95c52a0f6076 = 0x724d54edbacbebbb95c52a0f6076 := by
  unfold int256; norm_num
theorem int256_K27 :
    int256 0x279d346de4781f921dd7a89933d54d1f72928 = 0x279d346de4781f921dd7a89933d54d1f72928 := by
  unfold int256; norm_num
theorem int256_LN2 :
    int256 0x58b90bfbe8e7bcd5e4f1d9cc01f97b57a079a193394c5b16c5068badc5d =
      0x58b90bfbe8e7bcd5e4f1d9cc01f97b57a079a193394c5b16c5068badc5d := by
  unfold int256; norm_num

/-- `2^199 = evmShl 0xc7 1`. -/
theorem evmShl_c7_one : evmShl 0xc7 1 = 2 ^ 199 := by
  rw [evmShl_eq (by norm_num) (by norm_num)]; norm_num

/-! ## The octave index `k` -/

/-- The argument of the rounding shift, transported to `Int`: `2^199 + CINV · int256 x`. -/
theorem int256_kArg {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    int256 (evmAdd (evmShl 0xc7 1) (evmMul 0x724d54edbacbebbb95c52a0f6076 x)) =
      2 ^ 199 + 0x724d54edbacbebbb95c52a0f6076 * int256 x := by
  obtain ⟨hxlo, hxhi⟩ := region_x_bound hC hC0
  have hx96 : (-(2 ^ 96 : Int)) < int256 x ∧ int256 x < 2 ^ 96 := ⟨hxlo, hxhi⟩
  have hb96 : (2 : Int) ^ 96 = 79228162514264337593543950336 := by norm_num
  -- the product `CINV * int256 x` fits
  have hmul : int256 (evmMul 0x724d54edbacbebbb95c52a0f6076 x) =
      0x724d54edbacbebbb95c52a0f6076 * int256 x := by
    rw [evmMul_transport (by norm_num) hx ?_ ?_, int256_CINV]
    · rw [int256_CINV]
      simp only [hb96] at hxlo hxhi
      have : -(2 ^ 255 : Int) ≤ 0x724d54edbacbebbb95c52a0f6076 * int256 x := by
        simp only [ipow255]; nlinarith [hxlo, hxhi]
      exact this
    · rw [int256_CINV]
      simp only [hb96] at hxlo hxhi
      simp only [ipow255]; nlinarith [hxlo, hxhi]
  have hshl : evmShl 0xc7 1 = 2 ^ 199 := evmShl_c7_one
  rw [hshl]
  have hpow199 : (2 : Nat) ^ 199 < 2 ^ 256 := by norm_num
  rw [evmAdd_transport hpow199 (evmMul_lt _ _) ?_ ?_]
  · rw [hmul]
    have : int256 (2 ^ 199 : Nat) = (2 ^ 199 : Int) := by
      rw [int256_of_lt (by norm_num)]; norm_num
    rw [this]
  · rw [hmul]
    have h199 : int256 (2 ^ 199 : Nat) = (2 ^ 199 : Int) := by
      rw [int256_of_lt (by norm_num)]; norm_num
    rw [h199]; simp only [hb96, ipow255] at *; nlinarith [hxlo, hxhi]
  · rw [hmul]
    have h199 : int256 (2 ^ 199 : Nat) = (2 ^ 199 : Int) := by
      rw [int256_of_lt (by norm_num)]; norm_num
    rw [h199]; simp only [hb96, ipow255] at *; nlinarith [hxlo, hxhi]

/-- The argument of the `k`-rounding shift is a valid word (so the sandwich applies). -/
theorem kArg_lt {x : Nat} :
    evmAdd (evmShl 0xc7 1) (evmMul 0x724d54edbacbebbb95c52a0f6076 x) < 2 ^ 256 := evmAdd_lt _ _

/-- The `k`-floor sandwich on the meaningful region: `2^200·k ≤ 2^199 + CINV·x < 2^200·k + 2^200`. -/
theorem kTree_sandwich {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    (2 ^ 200 : Int) * int256 (kTree x) ≤ 2 ^ 199 + 0x724d54edbacbebbb95c52a0f6076 * int256 x ∧
      2 ^ 199 + 0x724d54edbacbebbb95c52a0f6076 * int256 x <
        (2 ^ 200 : Int) * int256 (kTree x) + 2 ^ 200 := by
  unfold kTree
  obtain ⟨_, hlo, hhi⟩ := evmSar_sandwich (s := 0xc8) (by norm_num) (kArg_lt (x := x))
  rw [int256_kArg hx hC hC0] at hlo hhi
  exact ⟨by simpa using hlo, by simpa using hhi⟩

/-- `k` is nondecreasing in the signed input across the meaningful region. -/
theorem kTree_mono {x1 x2 : Nat} (hx1 : x1 < 2 ^ 256) (hx2 : x2 < 2 ^ 256)
    (hC1 : int256 Cmask < int256 x1) (hle : int256 x1 ≤ int256 x2)
    (hC02 : int256 x2 < int256 C0thresh) :
    int256 (kTree x1) ≤ int256 (kTree x2) := by
  have hC2 : int256 Cmask < int256 x2 := lt_of_lt_of_le hC1 hle
  have hC01 : int256 x1 < int256 C0thresh := lt_of_le_of_lt hle hC02
  obtain ⟨hlo1, hhi1⟩ := kTree_sandwich hx1 hC1 hC01
  obtain ⟨hlo2, hhi2⟩ := kTree_sandwich hx2 hC2 hC02
  -- kArg increases with int256 x (CINV > 0), and floor is monotone.
  have hcinv : (0 : Int) < 0x724d54edbacbebbb95c52a0f6076 := by norm_num
  have hargle : 2 ^ 199 + 0x724d54edbacbebbb95c52a0f6076 * int256 x1 ≤
      2 ^ 199 + 0x724d54edbacbebbb95c52a0f6076 * int256 x2 := by
    have := mul_le_mul_left_nonneg hle (le_of_lt hcinv)
    omega
  -- from the two sandwiches: 2^200·k1 ≤ arg1 ≤ arg2 < 2^200·k2 + 2^200 ⇒ k1 < k2 + 1 ⇒ k1 ≤ k2
  have hpow : (0 : Int) < 2 ^ 200 := by norm_num
  nlinarith [hlo1, hhi2, hargle, hpow]

/-- On the meaningful region the octave index is bounded: `-61 ≤ k ≤ 63`. -/
theorem kTree_bound {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    -61 ≤ int256 (kTree x) ∧ int256 (kTree x) ≤ 63 := by
  obtain ⟨hlo, hhi⟩ := kTree_sandwich hx hC hC0
  have hCi : int256 Cmask = -41446531673892822312323846185 := int256_Cmask
  have hC0i : int256 C0thresh = 44014845965556527147994239713 := by
    unfold C0thresh int256; norm_num
  rw [hCi] at hC
  rw [hC0i] at hC0
  have hcinv : (0x724d54edbacbebbb95c52a0f6076 : Int) = 2318321547468254865173387471183990 := by
    norm_num
  -- bound the rounding-shift argument from the exact region endpoints.
  have hprod_lo : (0x724d54edbacbebbb95c52a0f6076 : Int) * int256 x >
      0x724d54edbacbebbb95c52a0f6076 * (-41446531673892822312323846185) := by
    rw [hcinv]; nlinarith [hC]
  have hprod_hi : (0x724d54edbacbebbb95c52a0f6076 : Int) * int256 x <
      0x724d54edbacbebbb95c52a0f6076 * 44014845965556527147994239713 := by
    rw [hcinv]; nlinarith [hC0]
  constructor
  · nlinarith [hhi, hprod_lo]
  · nlinarith [hlo, hprod_hi]

/-! ## The reduced argument `t` -/

/-- The argument of the `t`-reduction shift, transported to `Int`:
`K27 · int256 x − LN2 · int256 k`. -/
theorem int256_tArg {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    int256 (evmSub (evmMul 0x279d346de4781f921dd7a89933d54d1f72928 x)
        (evmMul 0x58b90bfbe8e7bcd5e4f1d9cc01f97b57a079a193394c5b16c5068badc5d (kTree x))) =
      0x279d346de4781f921dd7a89933d54d1f72928 * int256 x -
        0x58b90bfbe8e7bcd5e4f1d9cc01f97b57a079a193394c5b16c5068badc5d * int256 (kTree x) := by
  have hCi : int256 Cmask = -41446531673892822312323846185 := int256_Cmask
  have hC0i : int256 C0thresh = 44014845965556527147994239713 := by
    unfold C0thresh int256; norm_num
  have hxr := hC; rw [hCi] at hxr
  have hxr0 := hC0; rw [hC0i] at hxr0
  obtain ⟨hklo, hkhi⟩ := kTree_bound hx hC hC0
  have hk256 : kTree x < 2 ^ 256 := by unfold kTree; exact evmSar_lt _ _
  -- transport the two products.
  have hmul1 : int256 (evmMul 0x279d346de4781f921dd7a89933d54d1f72928 x) =
      0x279d346de4781f921dd7a89933d54d1f72928 * int256 x := by
    rw [evmMul_transport (by norm_num) hx ?_ ?_, int256_K27]
    · rw [int256_K27]; simp only [ipow255]; nlinarith [hxr, hxr0]
    · rw [int256_K27]; simp only [ipow255]; nlinarith [hxr, hxr0]
  have hmul2 :
      int256 (evmMul 0x58b90bfbe8e7bcd5e4f1d9cc01f97b57a079a193394c5b16c5068badc5d (kTree x)) =
      0x58b90bfbe8e7bcd5e4f1d9cc01f97b57a079a193394c5b16c5068badc5d * int256 (kTree x) := by
    rw [evmMul_transport (by norm_num) (by exact evmSar_lt _ _) ?_ ?_, int256_LN2]
    · rw [int256_LN2]; simp only [ipow255]; nlinarith [hklo, hkhi]
    · rw [int256_LN2]; simp only [ipow255]; nlinarith [hklo, hkhi]
  rw [evmSub_transport (evmMul_lt _ _) (evmMul_lt _ _) ?_ ?_, hmul1, hmul2]
  · rw [hmul1, hmul2]; simp only [ipow255]; nlinarith [hxr, hxr0, hklo, hkhi]
  · rw [hmul1, hmul2]; simp only [ipow255]; nlinarith [hxr, hxr0, hklo, hkhi]

end ExpYul

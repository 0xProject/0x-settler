import ExpProof.Mono.Tree

/-!
# Octave-index and reduced-argument transports

On the wide region the input word `x` (canonical, `< 2^256`) has signed value strictly between the
`mulExpRay` zero clamp and its overflow guard, `(zeroMax, hi) ⊂ (−2^97, 2^97)`. This file
transports the first two kernel stages — the octave index `k = round(x/(10²⁷·ln2))` and the
reduced argument `t` — to closed `Int` forms via the no-overflow bounds, and proves `k` is
nondecreasing in `int256 x` and (for a fixed `k`) `t` is nondecreasing in `int256 x`.

The `expRayToWad` meaningful region `(Cmask, C0thresh)` is strictly inside the wide region, so
every transport specializes to it; the wad-named lemmas below are those instances.

Constants and their bit widths (so every product stays below `2^255`):
`CINV` 111 bits, `K27` 146 bits, `LN2` 235 bits, `|int256 x| < 2^97`, `k ∈ [-127, 125]`.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

/-- The `mulExpRay` live region: strictly between the zero clamp and the overflow guard. -/
abbrev WideRegion (x : Nat) : Prop :=
  int256 mulExpRayZeroMax < int256 x ∧ int256 x < int256 mulExpRayHi

/-- The `expRayToWad` meaningful region is contained in the wide region. -/
theorem wideRegion_of_wad {x : Nat} (hC : int256 Cmask < int256 x)
    (hC0 : int256 x < int256 C0thresh) : WideRegion x := by
  rw [int256_Cmask] at hC
  rw [int256_C0thresh] at hC0
  exact ⟨by rw [int256_mulExpRayZeroMax]; omega, by rw [int256_mulExpRayHi]; omega⟩

/-- The signed value of `x` on the wide region is bounded by `2^97`. -/
theorem region_x_bound_wide {x : Nat} (hW : WideRegion x) :
    -(2 ^ 97 : Int) < int256 x ∧ int256 x < 2 ^ 97 := by
  obtain ⟨hlo, hhi⟩ := hW
  rw [int256_mulExpRayZeroMax] at hlo
  rw [int256_mulExpRayHi] at hhi
  constructor <;> [skip; skip] <;>
    simp only [show (2:Int)^97 = 158456325028528675187087900672 from by norm_num] <;> omega

/-- The signed value of `x` on the meaningful region is bounded by `2^96`. -/
theorem region_x_bound {x : Nat} (hC : int256 Cmask < int256 x)
    (hC0 : int256 x < int256 C0thresh) :
    -(2 ^ 96 : Int) < int256 x ∧ int256 x < 2 ^ 96 := by
  rw [int256_Cmask] at hC
  have hC0' : int256 x < 45401140326676417766828703956 := by
    rw [int256_C0thresh] at hC0
    exact hC0
  constructor <;> [skip; skip] <;> simp only [show (2:Int)^96 = 79228162514264337593543950336 from by norm_num] <;> omega

theorem CINV_lt : (0x724d54edbacbebbb95c52a0f60 : Nat) < 2 ^ 112 := by norm_num
theorem K27_lt : (0x279d346de4781f921dd7a89933d54d1f72928 : Nat) < 2 ^ 146 := by norm_num
theorem LN2_lt : (0x58b90bfbe8e7bcd5e4f1d9cc01f97b57a079a193394c5b16c5068badc5d : Nat) < 2 ^ 235 := by
  norm_num

/-- `int256` of the constant `CINV` (it is below `2^255`, so the signed view is the literal). -/
theorem int256_CINV : int256 0x724d54edbacbebbb95c52a0f60 = 0x724d54edbacbebbb95c52a0f60 := by
  unfold int256; norm_num
theorem int256_K27 :
    int256 0x279d346de4781f921dd7a89933d54d1f72928 = 0x279d346de4781f921dd7a89933d54d1f72928 := by
  unfold int256; norm_num
theorem int256_LN2 :
    int256 0x58b90bfbe8e7bcd5e4f1d9cc01f97b57a079a193394c5b16c5068badc5d =
      0x58b90bfbe8e7bcd5e4f1d9cc01f97b57a079a193394c5b16c5068badc5d := by
  unfold int256; norm_num

/-- `2^191 = evmShl 0xbf 1`. -/
theorem evmShl_bf_one : evmShl 0xbf 1 = 2 ^ 191 := by
  rw [evmShl_eq (by norm_num) (by norm_num)]; norm_num

/-! ## The octave index `k` -/

/-- The argument of the rounding shift, transported to `Int`: `2^191 + CINV · int256 x`. -/
theorem int256_kArg_wide {x : Nat} (hx : x < 2 ^ 256) (hW : WideRegion x) :
    int256 (evmAdd (evmShl 0xbf 1) (evmMul 0x724d54edbacbebbb95c52a0f60 x)) =
      2 ^ 191 + 0x724d54edbacbebbb95c52a0f60 * int256 x := by
  obtain ⟨hxlo, hxhi⟩ := region_x_bound_wide hW
  have hb97 : (2 : Int) ^ 97 = 158456325028528675187087900672 := by norm_num
  -- the product `CINV * int256 x` fits
  have hmul : int256 (evmMul 0x724d54edbacbebbb95c52a0f60 x) =
      0x724d54edbacbebbb95c52a0f60 * int256 x := by
    rw [evmMul_transport (by norm_num) hx ?_ ?_, int256_CINV]
    · rw [int256_CINV]
      simp only [hb97] at hxlo hxhi
      have : -(2 ^ 255 : Int) ≤ 0x724d54edbacbebbb95c52a0f60 * int256 x := by
        simp only [ipow255]; nlinarith [hxlo, hxhi]
      exact this
    · rw [int256_CINV]
      simp only [hb97] at hxlo hxhi
      simp only [ipow255]; nlinarith [hxlo, hxhi]
  have hshl : evmShl 0xbf 1 = 2 ^ 191 := evmShl_bf_one
  rw [hshl]
  have hpow199 : (2 : Nat) ^ 191 < 2 ^ 256 := by norm_num
  rw [evmAdd_transport hpow199 (evmMul_lt _ _) ?_ ?_]
  · rw [hmul]
    have : int256 (2 ^ 191 : Nat) = (2 ^ 191 : Int) := by
      rw [int256_of_lt (by norm_num)]; norm_num
    rw [this]
  · rw [hmul]
    have h199 : int256 (2 ^ 191 : Nat) = (2 ^ 191 : Int) := by
      rw [int256_of_lt (by norm_num)]; norm_num
    rw [h199]; simp only [hb97, ipow255] at *; nlinarith [hxlo, hxhi]
  · rw [hmul]
    have h199 : int256 (2 ^ 191 : Nat) = (2 ^ 191 : Int) := by
      rw [int256_of_lt (by norm_num)]; norm_num
    rw [h199]; simp only [hb97, ipow255] at *; nlinarith [hxlo, hxhi]

theorem int256_kArg {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    int256 (evmAdd (evmShl 0xbf 1) (evmMul 0x724d54edbacbebbb95c52a0f60 x)) =
      2 ^ 191 + 0x724d54edbacbebbb95c52a0f60 * int256 x :=
  int256_kArg_wide hx (wideRegion_of_wad hC hC0)

/-- The argument of the `k`-rounding shift is a valid word (so the sandwich applies). -/
theorem kArg_lt {x : Nat} :
    evmAdd (evmShl 0xbf 1) (evmMul 0x724d54edbacbebbb95c52a0f60 x) < 2 ^ 256 := evmAdd_lt _ _

/-- The `k`-floor sandwich on the wide region: `2^192·k ≤ 2^191 + CINV·x < 2^192·k + 2^192`. -/
theorem kTree_sandwich_wide {x : Nat} (hx : x < 2 ^ 256) (hW : WideRegion x) :
    (2 ^ 192 : Int) * int256 (kTree x) ≤ 2 ^ 191 + 0x724d54edbacbebbb95c52a0f60 * int256 x ∧
      2 ^ 191 + 0x724d54edbacbebbb95c52a0f60 * int256 x <
        (2 ^ 192 : Int) * int256 (kTree x) + 2 ^ 192 := by
  unfold kTree
  obtain ⟨_, hlo, hhi⟩ := evmSar_sandwich (s := 0xc0) (by norm_num) (kArg_lt (x := x))
  rw [int256_kArg_wide hx hW] at hlo hhi
  exact ⟨by simpa using hlo, by simpa using hhi⟩

theorem kTree_sandwich {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    (2 ^ 192 : Int) * int256 (kTree x) ≤ 2 ^ 191 + 0x724d54edbacbebbb95c52a0f60 * int256 x ∧
      2 ^ 191 + 0x724d54edbacbebbb95c52a0f60 * int256 x <
        (2 ^ 192 : Int) * int256 (kTree x) + 2 ^ 192 :=
  kTree_sandwich_wide hx (wideRegion_of_wad hC hC0)

/-- `k` is nondecreasing in the signed input across the wide region. -/
theorem kTree_mono_wide {x1 x2 : Nat} (hx1 : x1 < 2 ^ 256) (hx2 : x2 < 2 ^ 256)
    (hW1lo : int256 mulExpRayZeroMax < int256 x1) (hle : int256 x1 ≤ int256 x2)
    (hW2hi : int256 x2 < int256 mulExpRayHi) :
    int256 (kTree x1) ≤ int256 (kTree x2) := by
  have hW1 : WideRegion x1 := ⟨hW1lo, lt_of_le_of_lt hle hW2hi⟩
  have hW2 : WideRegion x2 := ⟨lt_of_lt_of_le hW1lo hle, hW2hi⟩
  obtain ⟨hlo1, hhi1⟩ := kTree_sandwich_wide hx1 hW1
  obtain ⟨hlo2, hhi2⟩ := kTree_sandwich_wide hx2 hW2
  -- kArg increases with int256 x (CINV > 0), and floor is monotone.
  have hcinv : (0 : Int) < 0x724d54edbacbebbb95c52a0f60 := by norm_num
  have hargle : 2 ^ 191 + 0x724d54edbacbebbb95c52a0f60 * int256 x1 ≤
      2 ^ 191 + 0x724d54edbacbebbb95c52a0f60 * int256 x2 := by
    have := mul_le_mul_left_nonneg hle (le_of_lt hcinv)
    omega
  -- from the two sandwiches: 2^192·k1 ≤ arg1 ≤ arg2 < 2^192·k2 + 2^192 ⇒ k1 < k2 + 1 ⇒ k1 ≤ k2
  have hpow : (0 : Int) < 2 ^ 192 := by norm_num
  nlinarith [hlo1, hhi2, hargle, hpow]

theorem kTree_mono {x1 x2 : Nat} (hx1 : x1 < 2 ^ 256) (hx2 : x2 < 2 ^ 256)
    (hC1 : int256 Cmask < int256 x1) (hle : int256 x1 ≤ int256 x2)
    (hC02 : int256 x2 < int256 C0thresh) :
    int256 (kTree x1) ≤ int256 (kTree x2) := by
  refine kTree_mono_wide hx1 hx2 ?_ hle ?_
  · rw [int256_mulExpRayZeroMax]; rw [int256_Cmask] at hC1; omega
  · rw [int256_mulExpRayHi]; rw [int256_C0thresh] at hC02; omega

/-- On the wide region the octave index is bounded: `-127 ≤ k ≤ 125`. The endpoints are exact:
the zero clamp sits at the least input whose octave count reaches `-127`, and the overflow guard
at the least input whose octave count reaches `126`. -/
theorem kTree_bound_wide {x : Nat} (hx : x < 2 ^ 256) (hW : WideRegion x) :
    -127 ≤ int256 (kTree x) ∧ int256 (kTree x) ≤ 125 := by
  obtain ⟨hlo, hhi⟩ := kTree_sandwich_wide hx hW
  obtain ⟨hC, hC0⟩ := hW
  rw [int256_mulExpRayZeroMax] at hC
  rw [int256_mulExpRayHi] at hC0
  have hcinv : (0x724d54edbacbebbb95c52a0f60 : Int) = 9055943544797870567083544809312 := by
    norm_num
  -- bound the rounding-shift argument from the exact region endpoints.
  have hprod_lo : (0x724d54edbacbebbb95c52a0f60 : Int) * int256 x >
      0x724d54edbacbebbb95c52a0f60 * (-88376265521393026950697095485) := by
    rw [hcinv]; nlinarith [hC]
  have hprod_hi : (0x724d54edbacbebbb95c52a0f60 : Int) * int256 x <
      0x724d54edbacbebbb95c52a0f60 * 86989971160273136331862631244 := by
    rw [hcinv]; nlinarith [hC0]
  constructor
  · nlinarith [hhi, hprod_lo]
  · nlinarith [hlo, hprod_hi]

/-- On the meaningful region the octave index is bounded: `-61 ≤ k ≤ 65`. -/
theorem kTree_bound {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    -61 ≤ int256 (kTree x) ∧ int256 (kTree x) ≤ 65 := by
  obtain ⟨hlo, hhi⟩ := kTree_sandwich hx hC hC0
  have hCi : int256 Cmask = -41446531673892822312323846185 := int256_Cmask
  have hC0i : int256 C0thresh = 45401140326676417766828703956 := int256_C0thresh
  rw [hCi] at hC
  rw [hC0i] at hC0
  have hcinv : (0x724d54edbacbebbb95c52a0f60 : Int) = 9055943544797870567083544809312 := by
    norm_num
  -- bound the rounding-shift argument from the exact region endpoints.
  have hprod_lo : (0x724d54edbacbebbb95c52a0f60 : Int) * int256 x >
      0x724d54edbacbebbb95c52a0f60 * (-41446531673892822312323846185) := by
    rw [hcinv]; nlinarith [hC]
  have hprod_hi : (0x724d54edbacbebbb95c52a0f60 : Int) * int256 x <
      0x724d54edbacbebbb95c52a0f60 * 45401140326676417766828703956 := by
    rw [hcinv]; nlinarith [hC0]
  constructor
  · nlinarith [hhi, hprod_lo]
  · nlinarith [hlo, hprod_hi]

/-! ## The reduced argument `t` -/

/-- The argument of the `t`-reduction shift, transported to `Int`:
`K27 · int256 x − LN2 · int256 k`. -/
theorem int256_tArg_wide {x : Nat} (hx : x < 2 ^ 256) (hW : WideRegion x) :
    int256 (evmSub (evmMul 0x279d346de4781f921dd7a89933d54d1f72928 x)
        (evmMul 0x58b90bfbe8e7bcd5e4f1d9cc01f97b57a079a193394c5b16c5068badc5d (kTree x))) =
      0x279d346de4781f921dd7a89933d54d1f72928 * int256 x -
        0x58b90bfbe8e7bcd5e4f1d9cc01f97b57a079a193394c5b16c5068badc5d * int256 (kTree x) := by
  obtain ⟨hxlo, hxhi⟩ := region_x_bound_wide hW
  have hb97 : (2 : Int) ^ 97 = 158456325028528675187087900672 := by norm_num
  rw [hb97] at hxlo hxhi
  obtain ⟨hklo, hkhi⟩ := kTree_bound_wide hx hW
  have hk256 : kTree x < 2 ^ 256 := by unfold kTree; exact evmSar_lt _ _
  -- transport the two products.
  have hmul1 : int256 (evmMul 0x279d346de4781f921dd7a89933d54d1f72928 x) =
      0x279d346de4781f921dd7a89933d54d1f72928 * int256 x := by
    rw [evmMul_transport (by norm_num) hx ?_ ?_, int256_K27]
    · rw [int256_K27]; simp only [ipow255]; nlinarith [hxlo, hxhi]
    · rw [int256_K27]; simp only [ipow255]; nlinarith [hxlo, hxhi]
  have hmul2 :
      int256 (evmMul 0x58b90bfbe8e7bcd5e4f1d9cc01f97b57a079a193394c5b16c5068badc5d (kTree x)) =
      0x58b90bfbe8e7bcd5e4f1d9cc01f97b57a079a193394c5b16c5068badc5d * int256 (kTree x) := by
    rw [evmMul_transport (by norm_num) (by exact evmSar_lt _ _) ?_ ?_, int256_LN2]
    · rw [int256_LN2]; simp only [ipow255]; nlinarith [hklo, hkhi]
    · rw [int256_LN2]; simp only [ipow255]; nlinarith [hklo, hkhi]
  rw [evmSub_transport (evmMul_lt _ _) (evmMul_lt _ _) ?_ ?_, hmul1, hmul2]
  · rw [hmul1, hmul2]; simp only [ipow255]; nlinarith [hxlo, hxhi, hklo, hkhi]
  · rw [hmul1, hmul2]; simp only [ipow255]; nlinarith [hxlo, hxhi, hklo, hkhi]

theorem int256_tArg {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    int256 (evmSub (evmMul 0x279d346de4781f921dd7a89933d54d1f72928 x)
        (evmMul 0x58b90bfbe8e7bcd5e4f1d9cc01f97b57a079a193394c5b16c5068badc5d (kTree x))) =
      0x279d346de4781f921dd7a89933d54d1f72928 * int256 x -
        0x58b90bfbe8e7bcd5e4f1d9cc01f97b57a079a193394c5b16c5068badc5d * int256 (kTree x) :=
  int256_tArg_wide hx (wideRegion_of_wad hC hC0)

/-- The `t`-reduction shift argument is a valid word. -/
theorem tArg_lt {x : Nat} :
    evmSub (evmMul 0x279d346de4781f921dd7a89933d54d1f72928 x)
        (evmMul 0x58b90bfbe8e7bcd5e4f1d9cc01f97b57a079a193394c5b16c5068badc5d (kTree x))
      < 2 ^ 256 := evmSub_lt _ _

/-- `t = sar(106, tArg)` floor sandwich: `2^106·t ≤ K27·x − LN2·k < 2^106·t + 2^106`. -/
theorem tTree_sandwich_wide {x : Nat} (hx : x < 2 ^ 256) (hW : WideRegion x) :
    (2 ^ 106 : Int) * int256 (tTree x) ≤
        0x279d346de4781f921dd7a89933d54d1f72928 * int256 x -
          0x58b90bfbe8e7bcd5e4f1d9cc01f97b57a079a193394c5b16c5068badc5d * int256 (kTree x) ∧
      0x279d346de4781f921dd7a89933d54d1f72928 * int256 x -
          0x58b90bfbe8e7bcd5e4f1d9cc01f97b57a079a193394c5b16c5068badc5d * int256 (kTree x) <
        (2 ^ 106 : Int) * int256 (tTree x) + 2 ^ 106 := by
  unfold tTree
  obtain ⟨_, hlo, hhi⟩ := evmSar_sandwich (s := 0x6a) (by norm_num) (tArg_lt (x := x))
  rw [int256_tArg_wide hx hW] at hlo hhi
  exact ⟨by simpa using hlo, by simpa using hhi⟩

theorem tTree_sandwich {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    (2 ^ 106 : Int) * int256 (tTree x) ≤
        0x279d346de4781f921dd7a89933d54d1f72928 * int256 x -
          0x58b90bfbe8e7bcd5e4f1d9cc01f97b57a079a193394c5b16c5068badc5d * int256 (kTree x) ∧
      0x279d346de4781f921dd7a89933d54d1f72928 * int256 x -
          0x58b90bfbe8e7bcd5e4f1d9cc01f97b57a079a193394c5b16c5068badc5d * int256 (kTree x) <
        (2 ^ 106 : Int) * int256 (tTree x) + 2 ^ 106 :=
  tTree_sandwich_wide hx (wideRegion_of_wad hC hC0)

/-- Within a fixed octave (`k` constant), `t` is nondecreasing in the signed input
(`K27 > 0`, and the floor of an increasing affine map is monotone). -/
theorem tTree_mono_sameOctave_wide {x1 x2 : Nat} (hx1 : x1 < 2 ^ 256) (hx2 : x2 < 2 ^ 256)
    (hW1 : WideRegion x1) (hW2 : WideRegion x2)
    (hk : int256 (kTree x1) = int256 (kTree x2)) (hle : int256 x1 ≤ int256 x2) :
    int256 (tTree x1) ≤ int256 (tTree x2) := by
  obtain ⟨hlo1, hhi1⟩ := tTree_sandwich_wide hx1 hW1
  obtain ⟨hlo2, hhi2⟩ := tTree_sandwich_wide hx2 hW2
  rw [hk] at hlo1 hhi1
  have hk27 : (0 : Int) < 0x279d346de4781f921dd7a89933d54d1f72928 := by norm_num
  have hargle : 0x279d346de4781f921dd7a89933d54d1f72928 * int256 x1 -
        0x58b90bfbe8e7bcd5e4f1d9cc01f97b57a079a193394c5b16c5068badc5d * int256 (kTree x2) ≤
      0x279d346de4781f921dd7a89933d54d1f72928 * int256 x2 -
        0x58b90bfbe8e7bcd5e4f1d9cc01f97b57a079a193394c5b16c5068badc5d * int256 (kTree x2) := by
    have := mul_le_mul_left_nonneg hle (le_of_lt hk27)
    omega
  have hpow : (0 : Int) < 2 ^ 106 := by norm_num
  nlinarith [hlo1, hhi2, hargle, hpow]

theorem tTree_mono_sameOctave {x1 x2 : Nat} (hx1 : x1 < 2 ^ 256) (hx2 : x2 < 2 ^ 256)
    (hC1 : int256 Cmask < int256 x1) (hC01 : int256 x1 < int256 C0thresh)
    (hC2 : int256 Cmask < int256 x2) (hC02 : int256 x2 < int256 C0thresh)
    (hk : int256 (kTree x1) = int256 (kTree x2)) (hle : int256 x1 ≤ int256 x2) :
    int256 (tTree x1) ≤ int256 (tTree x2) :=
  tTree_mono_sameOctave_wide hx1 hx2 (wideRegion_of_wad hC1 hC01) (wideRegion_of_wad hC2 hC02)
    hk hle

end ExpYul

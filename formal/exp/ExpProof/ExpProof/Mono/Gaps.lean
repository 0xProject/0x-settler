import ExpProof.Mono.Lipschitz

/-!
# Reduced-argument and squared-argument step gaps for adjacent same-octave inputs

For two inputs adjacent in the signed order (`int256 x2 = int256 x1 + 1`) lying in a common octave
(`kTree x1 = kTree x2`), the reduced argument advances by a fixed step:

```
G ≤ int256 (tTree x2) − int256 (tTree x1) ≤ G + 1,    G = ⌊K27 / 2^106⌋ = 680564733841.
```

From that, the squared argument `v = ⌊t²/2^133⌋` (which drives the even/odd accumulators) moves by
at most `W = ⌊(G + 1)/2^5⌋ + 1`: `|t2² − t1²| = |t2 − t1|·|t2 + t1| < (G + 1)·2^128` since
`|t| < 2^127`, and the common-denominator floor loses at most one unit at the `2^133` scale.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

/-- `K27 = G·2^106 + r` with `0 < r < 2^106`: the reduced-argument constant's quotient by the
shift is exactly `G`. -/
theorem K27_decomp :
    (0x279d346de4781f921dd7a89933d54d1f72928 : Int) =
      Gstep * 2 ^ 106 + 71144764483196081852107598539048 := by
  unfold Gstep; norm_num

theorem Gstep_rem_pos : (0 : Int) < 71144764483196081852107598539048 := by norm_num
theorem Gstep_rem_lt : (71144764483196081852107598539048 : Int) < 2 ^ 106 := by norm_num

/-- The reduced-argument step for adjacent same-octave inputs is `G` or `G + 1`. -/
theorem tTree_step {x1 x2 : Nat} (hx1 : x1 < 2 ^ 256) (hx2 : x2 < 2 ^ 256)
    (hC1 : int256 Cmask < int256 x1) (hC01 : int256 x1 < int256 C0thresh)
    (hC2 : int256 Cmask < int256 x2) (hC02 : int256 x2 < int256 C0thresh)
    (hk : int256 (kTree x1) = int256 (kTree x2))
    (hadj : int256 x2 = int256 x1 + 1) :
    (Gstep : Int) ≤ int256 (tTree x2) - int256 (tTree x1) ∧
      int256 (tTree x2) - int256 (tTree x1) ≤ Gstep + 1 := by
  obtain ⟨hlo1, hhi1⟩ := tTree_sandwich hx1 hC1 hC01
  obtain ⟨hlo2, hhi2⟩ := tTree_sandwich hx2 hC2 hC02
  rw [hk] at hlo1 hhi1
  -- the `K27·x − LN2·k` term advances by exactly `K27` from x1 to x2
  have hK27 := K27_decomp
  have hp107 : (0 : Int) < 2 ^ 106 := by norm_num
  set K27 := (0x279d346de4781f921dd7a89933d54d1f72928 : Int) with hK27def
  set LN2 := (0x58b90bfbe8e7bcd5e4f1d9cc01f97b57a079a193394c5b16c5068badc5d : Int) with hLN2def
  set k := int256 (kTree x2)
  set t1 := int256 (tTree x1)
  set t2 := int256 (tTree x2)
  set X1 := int256 x1
  set X2 := int256 x2
  -- the affine value at x2 exceeds that at x1 by exactly K27
  have hstep : K27 * X2 - LN2 * k = (K27 * X1 - LN2 * k) + K27 := by rw [hadj]; ring
  rw [hstep] at hlo2 hhi2
  -- combine: 2^106·t1 ≤ A < 2^106·t1 + 2^106 and 2^106·t2 ≤ A + K27 < 2^106·t2 + 2^106
  set A := K27 * X1 - LN2 * k
  -- with K27 = G·2^107 + r, 0 < r < 2^107
  have hrem_pos := Gstep_rem_pos
  have hrem_lt := Gstep_rem_lt
  constructor
  · nlinarith [hlo1, hhi1, hlo2, hhi2, hK27, hrem_pos, hrem_lt, hp107]
  · nlinarith [hlo1, hhi1, hlo2, hhi2, hK27, hrem_pos, hrem_lt, hp107]

/-- The squared-argument floor sandwich: `2^135·v ≤ t² < 2^135·v + 2^135`, from `vTree_eq`. -/
theorem vTree_sandwich {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    (2 ^ 135 : Int) * (vTree x : Int) ≤ (int256 (tTree x)) ^ 2 ∧
      (int256 (tTree x)) ^ 2 < (2 ^ 135 : Int) * (vTree x : Int) + 2 ^ 135 := by
  obtain ⟨hveq, _⟩ := vTree_eq hx hC hC0
  rw [hveq]
  set a := (int256 (tTree x)) ^ 2 with ha
  have h1 := Int.ediv_add_emod a (2 ^ 135)
  have h2 := Int.emod_nonneg a (by norm_num : (2 : Int) ^ 135 ≠ 0)
  have h3 := Int.emod_lt_of_pos a (by norm_num : (0 : Int) < 2 ^ 135)
  constructor <;> nlinarith [h1, h2, h3]

/-- The squared-argument step width `W = ⌊(G + 1)/2^6⌋ + 1`: one `v` unit is `2^135` of `t²`, so
the reduced-argument step `G + 1` moves `v` by at most `(G + 1)·2^129/2^135` plus one floor unit. -/
def Wstep : Nat := 10633823967

theorem Wstep_eq : Wstep = (Gstep + 1) / 2 ^ 6 + 1 := by unfold Wstep Gstep; rfl

/-- The squared-argument step for adjacent same-octave inputs is bounded by `W`. -/
theorem vTree_step {x1 x2 : Nat} (hx1 : x1 < 2 ^ 256) (hx2 : x2 < 2 ^ 256)
    (hC1 : int256 Cmask < int256 x1) (hC01 : int256 x1 < int256 C0thresh)
    (hC2 : int256 Cmask < int256 x2) (hC02 : int256 x2 < int256 C0thresh)
    (hk : int256 (kTree x1) = int256 (kTree x2))
    (hadj : int256 x2 = int256 x1 + 1) :
    -((Wstep : Int)) ≤ (vTree x2 : Int) - (vTree x1 : Int) ∧
      (vTree x2 : Int) - (vTree x1 : Int) ≤ Wstep := by
  obtain ⟨htg1, htg2⟩ := tTree_step hx1 hx2 hC1 hC01 hC2 hC02 hk hadj
  obtain ⟨htlo1, hthi1⟩ := tTree_bound hx1 hC1 hC01
  obtain ⟨htlo2, hthi2⟩ := tTree_bound hx2 hC2 hC02
  obtain ⟨hvlo1, hvhi1⟩ := vTree_sandwich hx1 hC1 hC01
  obtain ⟨hvlo2, hvhi2⟩ := vTree_sandwich hx2 hC2 hC02
  have hGpos : (0 : Int) ≤ Gstep := by unfold Gstep; norm_num
  have hp128 : (2 : Int) ^ 128 = 340282366920938463463374607431768211456 := by norm_num
  have hp135 : (2 : Int) ^ 135 = 43556142965880123323311949751266331066368 := by norm_num
  rw [hp128] at htlo1 hthi1 htlo2 hthi2
  rw [hp135] at hvlo1 hvhi1 hvlo2 hvhi2
  set t1 := int256 (tTree x1)
  set t2 := int256 (tTree x2)
  set v1 := (vTree x1 : Int)
  set v2 := (vTree x2 : Int)
  -- `t2² − t1² = (t2 − t1)(t2 + t1)`, with `|t2 − t1| ≤ G + 1`, `|t1 + t2| < 2^129`.
  have hsqdiff : t2 ^ 2 - t1 ^ 2 = (t2 - t1) * (t2 + t1) := by ring
  have hGv : (Gstep : Int) = 680564733841 := by unfold Gstep; norm_num
  have hWv : (Wstep : Int) = 10633823967 := by unfold Wstep; norm_num
  rw [hGv] at htg1 htg2
  rw [hWv]
  constructor
  · nlinarith [hvlo1, hvhi1, hvlo2, hvhi2, htg1, htg2, htlo1, hthi1, htlo2, hthi2, hsqdiff]
  · nlinarith [hvlo1, hvhi1, hvlo2, hvhi2, htg1, htg2, htlo1, hthi1, htlo2, hthi2, hsqdiff]

/-- The reduced-argument step on the wide region: `G` or `G + 1`. -/
theorem tTree_step_wide {x1 x2 : Nat} (hx1 : x1 < 2 ^ 256) (hx2 : x2 < 2 ^ 256)
    (hW1 : WideRegion x1) (hW2 : WideRegion x2)
    (hk : int256 (kTree x1) = int256 (kTree x2))
    (hadj : int256 x2 = int256 x1 + 1) :
    (Gstep : Int) ≤ int256 (tTree x2) - int256 (tTree x1) ∧
      int256 (tTree x2) - int256 (tTree x1) ≤ Gstep + 1 := by
  obtain ⟨hlo1, hhi1⟩ := tTree_sandwich_wide hx1 hW1
  obtain ⟨hlo2, hhi2⟩ := tTree_sandwich_wide hx2 hW2
  rw [hk] at hlo1 hhi1
  have hK27 := K27_decomp
  have hp107 : (0 : Int) < 2 ^ 106 := by norm_num
  set K27 := (0x279d346de4781f921dd7a89933d54d1f72928 : Int) with hK27def
  set LN2 := (0x58b90bfbe8e7bcd5e4f1d9cc01f97b57a079a193394c5b16c5068badc5d : Int) with hLN2def
  set k := int256 (kTree x2)
  set t1 := int256 (tTree x1)
  set t2 := int256 (tTree x2)
  set X1 := int256 x1
  set X2 := int256 x2
  have hstep : K27 * X2 - LN2 * k = (K27 * X1 - LN2 * k) + K27 := by rw [hadj]; ring
  rw [hstep] at hlo2 hhi2
  set A := K27 * X1 - LN2 * k
  have hrem_pos := Gstep_rem_pos
  have hrem_lt := Gstep_rem_lt
  constructor
  · nlinarith [hlo1, hhi1, hlo2, hhi2, hK27, hrem_pos, hrem_lt, hp107]
  · nlinarith [hlo1, hhi1, hlo2, hhi2, hK27, hrem_pos, hrem_lt, hp107]

/-- The squared-argument floor sandwich on the wide region. -/
theorem vTree_sandwich_wide {x : Nat} (hx : x < 2 ^ 256) (hW : WideRegion x) :
    (2 ^ 135 : Int) * (vTree x : Int) ≤ (int256 (tTree x)) ^ 2 ∧
      (int256 (tTree x)) ^ 2 < (2 ^ 135 : Int) * (vTree x : Int) + 2 ^ 135 := by
  obtain ⟨hveq, _⟩ := vTree_eq_wide hx hW
  rw [hveq]
  set a := (int256 (tTree x)) ^ 2 with ha
  have h1 := Int.ediv_add_emod a (2 ^ 135)
  have h2 := Int.emod_nonneg a (by norm_num : (2 : Int) ^ 135 ≠ 0)
  have h3 := Int.emod_lt_of_pos a (by norm_num : (0 : Int) < 2 ^ 135)
  constructor <;> nlinarith [h1, h2, h3]

/-- The squared-argument step on the wide region is bounded by `W`. -/
theorem vTree_step_wide {x1 x2 : Nat} (hx1 : x1 < 2 ^ 256) (hx2 : x2 < 2 ^ 256)
    (hW1 : WideRegion x1) (hW2 : WideRegion x2)
    (hk : int256 (kTree x1) = int256 (kTree x2))
    (hadj : int256 x2 = int256 x1 + 1) :
    -((Wstep : Int)) ≤ (vTree x2 : Int) - (vTree x1 : Int) ∧
      (vTree x2 : Int) - (vTree x1 : Int) ≤ Wstep := by
  obtain ⟨htg1, htg2⟩ := tTree_step_wide hx1 hx2 hW1 hW2 hk hadj
  obtain ⟨htlo1, hthi1⟩ := tTree_bound_wide hx1 hW1
  obtain ⟨htlo2, hthi2⟩ := tTree_bound_wide hx2 hW2
  obtain ⟨hvlo1, hvhi1⟩ := vTree_sandwich_wide hx1 hW1
  obtain ⟨hvlo2, hvhi2⟩ := vTree_sandwich_wide hx2 hW2
  have hGpos : (0 : Int) ≤ Gstep := by unfold Gstep; norm_num
  have hp128 : (2 : Int) ^ 128 = 340282366920938463463374607431768211456 := by norm_num
  have hp135 : (2 : Int) ^ 135 = 43556142965880123323311949751266331066368 := by norm_num
  rw [hp128] at htlo1 hthi1 htlo2 hthi2
  rw [hp135] at hvlo1 hvhi1 hvlo2 hvhi2
  set t1 := int256 (tTree x1)
  set t2 := int256 (tTree x2)
  set v1 := (vTree x1 : Int)
  set v2 := (vTree x2 : Int)
  have hsqdiff : t2 ^ 2 - t1 ^ 2 = (t2 - t1) * (t2 + t1) := by ring
  have hGv : (Gstep : Int) = 680564733841 := by unfold Gstep; norm_num
  have hWv : (Wstep : Int) = 10633823967 := by unfold Wstep; norm_num
  rw [hGv] at htg1 htg2
  rw [hWv]
  constructor
  · nlinarith [hvlo1, hvhi1, hvlo2, hvhi2, htg1, htg2, htlo1, hthi1, htlo2, hthi2, hsqdiff]
  · nlinarith [hvlo1, hvhi1, hvlo2, hvhi2, htg1, htg2, htlo1, hthi1, htlo2, hthi2, hsqdiff]

end ExpYul

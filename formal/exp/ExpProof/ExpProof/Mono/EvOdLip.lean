import ExpProof.Mono.Gaps

/-!
# Near-constancy of the even/odd accumulators across adjacent inputs

Telescoping `stage_lip` through the five even / four odd Horner stages, with the squared-argument
gap `|v2 − v1| ≤ W = G + 1` from `vTree_step`, bounds the change of the accumulators:

```
|evTree x2 − evTree x1| ≤ DEv = 42701611664,
|odTree x2 − odTree x1| ≤ DOd = 5327301648.
```

The intermediate per-stage prev bounds reuse the chained `2^k` ceilings established inside
`evTree_facts`/`odTree_facts`; each stage application keeps the accumulator words opaque so the
deep tree is never forced.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

/-- Two-sided distance abbreviation. -/
def dist_le (a b D : Nat) : Prop := a ≤ b + D ∧ b ≤ a + D

theorem dist_le.symm {a b D : Nat} (h : dist_le a b D) : dist_le b a D := ⟨h.2, h.1⟩

/-- The leading even stage `a4 + ⌊v/2^29⌋` moves by at most `(W >> 0x1d) + 1` under `|v2−v1| ≤ W`. -/
theorem evLead_lip {c v1 v2 W : Nat} (hc : c < 2 ^ 255) (hv1 : v1 < 2 ^ 126) (hv2 : v2 < 2 ^ 126)
    (hvg1 : v1 ≤ v2 + W) (hvg2 : v2 ≤ v1 + W) :
    dist_le (evmAdd c (evmShr 0x1d v1)) (evmAdd c (evmShr 0x1d v2)) ((W / 2 ^ 0x1d) + 1) := by
  have hd1 : evmShr 0x1d v1 = v1 / 2 ^ 0x1d := evmShr_eq_div (by norm_num) (by omega)
  have hd2 : evmShr 0x1d v2 = v2 / 2 ^ 0x1d := evmShr_eq_div (by norm_num) (by omega)
  have hsh0 : (0 : Nat) < 2 ^ 0x1d := Nat.two_pow_pos _
  -- `v/2^29 < 2^97`, so the sum fits below `2^256`
  have hb1 : v1 / 2 ^ 0x1d < 2 ^ 97 := by
    have : v1 / 2 ^ 0x1d < 2 ^ 126 / 2 ^ 0x1d := Nat.div_lt_div_of_lt_of_dvd (by norm_num) hv1
    have he : (2:Nat) ^ 126 / 2 ^ 0x1d = 2 ^ 97 := by rw [Nat.pow_div (by norm_num) (by norm_num)]
    omega
  have hb2 : v2 / 2 ^ 0x1d < 2 ^ 97 := by
    have : v2 / 2 ^ 0x1d < 2 ^ 126 / 2 ^ 0x1d := Nat.div_lt_div_of_lt_of_dvd (by norm_num) hv2
    have he : (2:Nat) ^ 126 / 2 ^ 0x1d = 2 ^ 97 := by rw [Nat.pow_div (by norm_num) (by norm_num)]
    omega
  have hlt1 : v1 / 2 ^ 0x1d < 2 ^ 256 := by
    have h : (2:Nat) ^ 97 < 2 ^ 256 := by norm_num
    omega
  have hlt2 : v2 / 2 ^ 0x1d < 2 ^ 256 := by
    have h : (2:Nat) ^ 97 < 2 ^ 256 := by norm_num
    omega
  have hc256 : c < 2 ^ 256 := by
    have h : (2:Nat) ^ 255 < 2 ^ 256 := by norm_num
    omega
  have hsm : (2:Nat)^255 + 2^97 < 2^256 := by norm_num
  have he1 : evmAdd c (evmShr 0x1d v1) = c + v1 / 2 ^ 0x1d := by
    rw [hd1, evmAdd_eq_nat hc256 hlt1 (by omega)]
  have he2 : evmAdd c (evmShr 0x1d v2) = c + v2 / 2 ^ 0x1d := by
    rw [hd2, evmAdd_eq_nat hc256 hlt2 (by omega)]
  rw [he1, he2]
  -- |v1/d − v2/d| ≤ |v1−v2|/d + 1 ≤ W/d + 1, via the additive floored-sum bound
  have h12 : v1 / 2 ^ 0x1d ≤ v2 / 2 ^ 0x1d + (W / 2 ^ 0x1d + 1) := by
    have s1 : v1 / 2 ^ 0x1d ≤ (v2 + W) / 2 ^ 0x1d := Nat.div_le_div_right hvg1
    have s2 := add_div_le_add (b := v2) (n := W) hsh0
    omega
  have h21 : v2 / 2 ^ 0x1d ≤ v1 / 2 ^ 0x1d + (W / 2 ^ 0x1d + 1) := by
    have s1 : v2 / 2 ^ 0x1d ≤ (v1 + W) / 2 ^ 0x1d := Nat.div_le_div_right hvg2
    have s2 := add_div_le_add (b := v1) (n := W) hsh0
    omega
  exact ⟨by omega, by omega⟩

/-- The leading odd stage is the bare constant `b4` (no `v`-dependence): distance `0`. -/
theorem odLead_const (c : Nat) : dist_le c c 0 := ⟨by omega, by omega⟩

/-- `stage_lip` repackaged in the `dist_le` form for a fixed stage shift. -/
theorem stage_lip_dist {c prev1 prev2 v1 v2 P Dprev W sh : Nat}
    (hp1 : prev1 ≤ P) (hp2 : prev2 ≤ P) (hv1 : v1 < 2 ^ 126) (hv2 : v2 < 2 ^ 126)
    (hvg1 : v1 ≤ v2 + W) (hvg2 : v2 ≤ v1 + W)
    (hpd : dist_le prev1 prev2 Dprev)
    (hPV : P * 2 ^ 126 < 2 ^ 256) (hsh : sh < 256)
    (hsum1 : c + P * 2 ^ 126 / 2 ^ sh < 2 ^ 256) :
    dist_le (evmAdd c (evmShr sh (evmMul prev1 v1))) (evmAdd c (evmShr sh (evmMul prev2 v2)))
      ((P * W + 2 ^ 126 * Dprev) / 2 ^ sh + 1) :=
  stage_lip hp1 hp2 hv1 hv2 hvg1 hvg2 hpd.1 hpd.2 hPV hsh hsum1

/-! ## The even Horner stages as named layers, with their `2^k` ceilings -/

def evS0 (x : Nat) : Nat := evmAdd 0xb9aacfad41060587203a79af0ebc (evmShr 0x1d (vTree x))
def evS1 (x : Nat) : Nat := evmAdd 0x9a036222e11aee18465042f8ea64c8 (evmShr 0x82 (evmMul (evS0 x) (vTree x)))
def evS2 (x : Nat) : Nat := evmAdd 0x9064d965e1c4863b73604e0ddbec53f9 (evmShr 0x80 (evmMul (evS1 x) (vTree x)))
def evS3 (x : Nat) : Nat := evmAdd 0x93f11e65781741b92fa7fc4f4fffcca2 (evmShr 0x86 (evmMul (evS2 x) (vTree x)))

theorem evTree_layers (x : Nat) :
    evTree x = evmAdd 0x4e14a45e8ec305e233e11b4174e214ac (evmShr 0x84 (evmMul (evS3 x) (vTree x))) :=
  rfl

theorem evS0_lt {x : Nat} (hv : vTree x < 2 ^ 126) : evS0 x < 2 ^ 113 := ev0_lt hv

theorem evS1_lt {x : Nat} (hv : vTree x < 2 ^ 126) : evS1 x < 2 ^ 121 := by
  have := (stage_bounds (c := 0x9a036222e11aee18465042f8ea64c8) (prev := evS0 x) (v := vTree x)
    (P := 2 ^ 113) (V := 2 ^ 126) (sh := 0x82) (evS0_lt hv) hv (by norm_num) (by norm_num)
    (by rw [pvd 113 126 130 109 (by norm_num)]; norm_num)).2
  rw [pvd 113 126 130 109 (by norm_num)] at this; unfold evS1; omega

theorem evS2_lt {x : Nat} (hv : vTree x < 2 ^ 126) : evS2 x < 2 ^ 129 := by
  have := (stage_bounds (c := 0x9064d965e1c4863b73604e0ddbec53f9) (prev := evS1 x) (v := vTree x)
    (P := 2 ^ 121) (V := 2 ^ 126) (sh := 0x80) (evS1_lt hv) hv (by norm_num) (by norm_num)
    (by rw [pvd 121 126 128 119 (by norm_num)]; norm_num)).2
  rw [pvd 121 126 128 119 (by norm_num)] at this; unfold evS2; omega

theorem evS3_lt {x : Nat} (hv : vTree x < 2 ^ 126) : evS3 x < 2 ^ 129 := by
  have := (stage_bounds (c := 0x93f11e65781741b92fa7fc4f4fffcca2) (prev := evS2 x) (v := vTree x)
    (P := 2 ^ 129) (V := 2 ^ 126) (sh := 0x86) (evS2_lt hv) hv (by norm_num) (by norm_num)
    (by rw [pvd 129 126 134 121 (by norm_num)]; norm_num)).2
  rw [pvd 129 126 134 121 (by norm_num)] at this; unfold evS3; omega

/-! ## The odd Horner stages as named layers -/

def odS0 (x : Nat) : Nat := evmAdd 0xc926ddbf3830ca5561cc01585402d0 (evmShr 0x83 (evmMul 0xdc07aff85e5bb5629d0fb64a84bb (vTree x)))
def odS1 (x : Nat) : Nat := evmAdd 0xad4506b00b1246c7e5b4fd33e1201b (evmShr 0x89 (evmMul (odS0 x) (vTree x)))
def odS2 (x : Nat) : Nat := evmAdd 0xaf5662483c4ce783a9ef5fe025f42e9e (evmShr 0x7f (evmMul (odS1 x) (vTree x)))

theorem odTree_layers (x : Nat) :
    odTree x = evmAdd 0x270a522f476182f119f08da0ba710a56 (evmShr 0x87 (evmMul (odS2 x) (vTree x))) :=
  rfl

theorem odS0_lt {x : Nat} (hv : vTree x < 2 ^ 126) : odS0 x < 2 ^ 121 := by
  have := (stage_bounds (c := 0xc926ddbf3830ca5561cc01585402d0) (prev := 0xdc07aff85e5bb5629d0fb64a84bb)
    (v := vTree x) (P := 2 ^ 112) (V := 2 ^ 126) (sh := 0x83) (by norm_num) hv (by norm_num)
    (by norm_num) (by rw [pvd 112 126 131 107 (by norm_num)]; norm_num)).2
  rw [pvd 112 126 131 107 (by norm_num)] at this; unfold odS0; omega

theorem odS1_lt {x : Nat} (hv : vTree x < 2 ^ 126) : odS1 x < 2 ^ 121 := by
  have := (stage_bounds (c := 0xad4506b00b1246c7e5b4fd33e1201b) (prev := odS0 x) (v := vTree x)
    (P := 2 ^ 121) (V := 2 ^ 126) (sh := 0x89) (odS0_lt hv) hv (by norm_num) (by norm_num)
    (by rw [pvd 121 126 137 110 (by norm_num)]; norm_num)).2
  rw [pvd 121 126 137 110 (by norm_num)] at this; unfold odS1; omega

theorem odS2_lt {x : Nat} (hv : vTree x < 2 ^ 126) : odS2 x < 2 ^ 129 := by
  have := (stage_bounds (c := 0xaf5662483c4ce783a9ef5fe025f42e9e) (prev := odS1 x) (v := vTree x)
    (P := 2 ^ 121) (V := 2 ^ 126) (sh := 0x7f) (odS1_lt hv) hv (by norm_num) (by norm_num)
    (by rw [pvd 121 126 127 120 (by norm_num)]; norm_num)).2
  rw [pvd 121 126 127 120 (by norm_num)] at this; unfold odS2; omega

/-! ## Composed Lipschitz bounds -/

/-- The step width `W = G + 1`. -/
def Wstep : Nat := 340282366921

theorem Wstep_eq : Wstep = Gstep + 1 := by unfold Wstep Gstep; rfl

/-- **Even accumulator near-constancy.** Under a squared-argument gap `|v2 − v1| ≤ W` the even
accumulator changes by at most `DEv = 42701611664`. -/
theorem evTree_lip {x1 x2 : Nat} (hv1 : vTree x1 < 2 ^ 126) (hv2 : vTree x2 < 2 ^ 126)
    (hg1 : vTree x1 ≤ vTree x2 + Wstep) (hg2 : vTree x2 ≤ vTree x1 + Wstep) :
    dist_le (evTree x1) (evTree x2) 42701611664 := by
  -- leading stage
  have d0 : dist_le (evS0 x1) (evS0 x2) 634 := by
    have h := evLead_lip (c := 0xb9aacfad41060587203a79af0ebc) (W := Wstep) (by norm_num) hv1 hv2 hg1 hg2
    have he : (Wstep / 2 ^ 0x1d) + 1 = 634 := by unfold Wstep; decide
    rw [he] at h; exact h
  -- stage 1
  have d1 : dist_le (evS1 x1) (evS1 x2) 2596189 := by
    have h := stage_lip_dist (c := 0x9a036222e11aee18465042f8ea64c8) (P := 2 ^ 113) (sh := 0x82) (W := Wstep)
      (Dprev := 634) (le_of_lt (evS0_lt hv1)) (le_of_lt (evS0_lt hv2)) hv1 hv2 hg1 hg2 d0
      (by norm_num) (by norm_num) (by norm_num)
    have he : (2 ^ 113 * Wstep + 2 ^ 126 * 634) / 2 ^ 0x82 + 1 = 2596189 := by unfold Wstep; decide
    rw [he] at h; exact h
  -- stage 2
  have d2 : dist_le (evS2 x1) (evS2 x2) 2659105039 := by
    have h := stage_lip_dist (c := 0x9064d965e1c4863b73604e0ddbec53f9) (P := 2 ^ 121) (sh := 0x80) (W := Wstep)
      (Dprev := 2596189) (le_of_lt (evS1_lt hv1)) (le_of_lt (evS1_lt hv2)) hv1 hv2 hg1 hg2 d1
      (by norm_num) (by norm_num) (by norm_num)
    have he : (2 ^ 121 * Wstep + 2 ^ 126 * 2596189) / 2 ^ 0x80 + 1 = 2659105039 := by
      unfold Wstep; decide
    rw [he] at h; exact h
  -- stage 3
  have d3 : dist_le (evS3 x1) (evS3 x2) 10644211096 := by
    have h := stage_lip_dist (c := 0x93f11e65781741b92fa7fc4f4fffcca2) (P := 2 ^ 129) (sh := 0x86) (W := Wstep)
      (Dprev := 2659105039) (le_of_lt (evS2_lt hv1)) (le_of_lt (evS2_lt hv2)) hv1 hv2 hg1 hg2 d2
      (by norm_num) (by norm_num) (by norm_num)
    have he : (2 ^ 129 * Wstep + 2 ^ 126 * 2659105039) / 2 ^ 0x86 + 1 = 10644211096 := by
      unfold Wstep; decide
    rw [he] at h; exact h
  -- final stage
  have hfin := stage_lip_dist (c := 0x4e14a45e8ec305e233e11b4174e214ac) (P := 2 ^ 129) (sh := 0x84) (W := Wstep)
    (Dprev := 10644211096) (le_of_lt (evS3_lt hv1)) (le_of_lt (evS3_lt hv2)) hv1 hv2 hg1 hg2 d3
    (by norm_num) (by norm_num) (by norm_num)
  have he : (2 ^ 129 * Wstep + 2 ^ 126 * 10644211096) / 2 ^ 0x84 + 1 = 42701611664 := by
    unfold Wstep; decide
  rw [he] at hfin
  rw [evTree_layers, evTree_layers]; exact hfin

/-- **Odd accumulator near-constancy.** Under a squared-argument gap `|v2 − v1| ≤ W` the odd
accumulator changes by at most `DOd = 5327301648`. -/
theorem odTree_lip {x1 x2 : Nat} (hv1 : vTree x1 < 2 ^ 126) (hv2 : vTree x2 < 2 ^ 126)
    (hg1 : vTree x1 ≤ vTree x2 + Wstep) (hg2 : vTree x2 ≤ vTree x1 + Wstep) :
    dist_le (odTree x1) (odTree x2) 5327301648 := by
  -- stage 0: prev is the constant leading coefficient (distance 0)
  have d0 : dist_le (odS0 x1) (odS0 x2) 649038 := by
    have h := stage_lip_dist (c := 0xc926ddbf3830ca5561cc01585402d0) (P := 2 ^ 112) (sh := 0x83) (W := Wstep)
      (Dprev := 0) (prev1 := 0xdc07aff85e5bb5629d0fb64a84bb) (prev2 := 0xdc07aff85e5bb5629d0fb64a84bb)
      (by norm_num) (by norm_num) hv1 hv2 hg1 hg2 (odLead_const _) (by norm_num) (by norm_num)
      (by norm_num)
    have he : (2 ^ 112 * Wstep + 2 ^ 126 * 0) / 2 ^ 0x83 + 1 = 649038 := by unfold Wstep; decide
    rw [he] at h; exact h
  have d1 : dist_le (odS1 x1) (odS1 x2) 5192614 := by
    have h := stage_lip_dist (c := 0xad4506b00b1246c7e5b4fd33e1201b) (P := 2 ^ 121) (sh := 0x89) (W := Wstep)
      (Dprev := 649038) (le_of_lt (odS0_lt hv1)) (le_of_lt (odS0_lt hv2)) hv1 hv2 hg1 hg2 d0
      (by norm_num) (by norm_num) (by norm_num)
    have he : (2 ^ 121 * Wstep + 2 ^ 126 * 649038) / 2 ^ 0x89 + 1 = 5192614 := by unfold Wstep; decide
    rw [he] at h; exact h
  have d2 : dist_le (odS2 x1) (odS2 x2) 5319508291 := by
    have h := stage_lip_dist (c := 0xaf5662483c4ce783a9ef5fe025f42e9e) (P := 2 ^ 121) (sh := 0x7f) (W := Wstep)
      (Dprev := 5192614) (le_of_lt (odS1_lt hv1)) (le_of_lt (odS1_lt hv2)) hv1 hv2 hg1 hg2 d1
      (by norm_num) (by norm_num) (by norm_num)
    have he : (2 ^ 121 * Wstep + 2 ^ 126 * 5192614) / 2 ^ 0x7f + 1 = 5319508291 := by
      unfold Wstep; decide
    rw [he] at h; exact h
  have hfin := stage_lip_dist (c := 0x270a522f476182f119f08da0ba710a56) (P := 2 ^ 129) (sh := 0x87) (W := Wstep)
    (Dprev := 5319508291) (le_of_lt (odS2_lt hv1)) (le_of_lt (odS2_lt hv2)) hv1 hv2 hg1 hg2 d2
    (by norm_num) (by norm_num) (by norm_num)
  have he : (2 ^ 129 * Wstep + 2 ^ 126 * 5319508291) / 2 ^ 0x87 + 1 = 5327301648 := by
    unfold Wstep; decide
  rw [he] at hfin
  rw [odTree_layers, odTree_layers]; exact hfin

end ExpYul

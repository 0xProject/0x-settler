import ExpProof.Mono.Gaps

/-!
# Near-constancy of the even/odd accumulators across adjacent inputs

Telescoping `stage_lip` through the five even / four odd Horner stages, with the squared-argument
gap `|v2 − v1| ≤ W` from `vTree_step`, bounds the change of the accumulators:

```
|evTree x2 − evTree x1| ≤ DEv = 42618413185,
|odTree x2 − odTree x1| ≤ DOd = 5322105549.
```

The intermediate per-stage prev bounds reuse the chained ceilings established inside
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

/-- The monic leading even stage `a4 + v` is a bare add: it moves by exactly the argument gap
`|v2 − v1| ≤ W`. -/
theorem evLead_lip {c v1 v2 W : Nat} (hc : c < 2 ^ 255) (hv1 : v1 < 2 ^ 120) (hv2 : v2 < 2 ^ 120)
    (hvg1 : v1 ≤ v2 + W) (hvg2 : v2 ≤ v1 + W) :
    dist_le (evmAdd c v1) (evmAdd c v2) W := by
  have he1 : evmAdd c v1 = c + v1 := evmAdd_eq_nat (by omega) (by omega) (by omega)
  have he2 : evmAdd c v2 = c + v2 := evmAdd_eq_nat (by omega) (by omega) (by omega)
  rw [he1, he2]
  exact ⟨by omega, by omega⟩

/-- The leading odd stage is the bare constant `b4` (no `v`-dependence): distance `0`. -/
theorem odLead_const (c : Nat) : dist_le c c 0 := ⟨by omega, by omega⟩

/-- `stage_lip` repackaged in the `dist_le` form for a fixed stage shift. -/
theorem stage_lip_dist {c prev1 prev2 v1 v2 P V Dprev W sh : Nat}
    (hp1 : prev1 ≤ P) (hp2 : prev2 ≤ P) (hv1 : v1 < V) (hv2 : v2 < V)
    (hvg1 : v1 ≤ v2 + W) (hvg2 : v2 ≤ v1 + W)
    (hpd : dist_le prev1 prev2 Dprev)
    (hPV : P * V < 2 ^ 256) (hsh : sh < 256)
    (hsum1 : c + P * V / 2 ^ sh < 2 ^ 256) (hVw : V < 2 ^ 256) :
    dist_le (evmAdd c (evmShr sh (evmMul prev1 v1))) (evmAdd c (evmShr sh (evmMul prev2 v2)))
      ((P * W + V * Dprev) / 2 ^ sh + 1) :=
  stage_lip hp1 hp2 hv1 hv2 hvg1 hvg2 hpd.1 hpd.2 hPV hsh hsum1 hVw

/-! ## The even Horner stages as named layers, with their chained ceilings -/

def evS0 (x : Nat) : Nat := evmAdd 0xb9aacfacf3c10b378435f8e22adf48500e (vTree x)
def evS1 (x : Nat) : Nat := evmAdd 0x9a036222841f47c6ed6fc3f7602053 (evmShr 0x95 (evmMul (evS0 x) (vTree x)))
def evS2 (x : Nat) : Nat := evmAdd 0x9064d9657e9a21fc16bb69331c5c3057 (evmShr 0x7b (evmMul (evS1 x) (vTree x)))
def evS3 (x : Nat) : Nat := evmAdd 0x93f11e650dd6c64b96ce79065cdf809e (evmShr 0x81 (evmMul (evS2 x) (vTree x)))

theorem evTree_layers (x : Nat) :
    evTree x = evmAdd 0x4e14a45e5650b506e97f4c5da23861e2 (evmShr 0x7f (evmMul (evS3 x) (vTree x))) :=
  rfl

theorem evS0_lt {x : Nat} (hv : vTree x < 2 ^ 120) :
    evS0 x < 0xb9aacfacf3c10b378435f8e22adf48500e + 2 ^ 120 := ev0_lt hv

theorem evS1_lt {x : Nat} (hv : vTree x < 2 ^ 120) : evS1 x < 2 ^ 121 := by
  have := (stage_bounds (c := 0x9a036222841f47c6ed6fc3f7602053) (prev := evS0 x) (v := vTree x)
    (P := 0xb9aacfacf3c10b378435f8e22adf48500e + 2 ^ 120) (V := 2 ^ 120) (sh := 0x95)
    (evS0_lt hv) hv (by norm_num) (by norm_num) (by norm_num)).2
  have hcap : (0x9a036222841f47c6ed6fc3f7602053 : Nat) +
      (0xb9aacfacf3c10b378435f8e22adf48500e + 2 ^ 120) * 2 ^ 120 / 2 ^ 0x95 < 2 ^ 121 := by
    norm_num
  unfold evS1; omega

theorem evS2_lt {x : Nat} (hv : vTree x < 2 ^ 120) : evS2 x < 2 ^ 129 := by
  have := (stage_bounds (c := 0x9064d9657e9a21fc16bb69331c5c3057) (prev := evS1 x) (v := vTree x)
    (P := 2 ^ 121) (V := 2 ^ 120) (sh := 0x7b) (evS1_lt hv) hv (by norm_num) (by norm_num)
    (by rw [pvd 121 120 123 118 (by norm_num)]; norm_num)).2
  rw [pvd 121 120 123 118 (by norm_num)] at this; unfold evS2; omega

theorem evS3_lt {x : Nat} (hv : vTree x < 2 ^ 120) : evS3 x < 2 ^ 129 := by
  have := (stage_bounds (c := 0x93f11e650dd6c64b96ce79065cdf809e) (prev := evS2 x) (v := vTree x)
    (P := 2 ^ 129) (V := 2 ^ 120) (sh := 0x81) (evS2_lt hv) hv (by norm_num) (by norm_num)
    (by rw [pvd 129 120 129 120 (by norm_num)]; norm_num)).2
  rw [pvd 129 120 129 120 (by norm_num)] at this; unfold evS3; omega

/-! ## The odd Horner stages as named layers -/

def odS0 (x : Nat) : Nat := evmAdd 0xc926ddbecdeeb42e68cd16db7da8c1 (evmShr 0x7e (evmMul 0xdc07aff8276bde9a361278df6a10 (vTree x)))
def odS1 (x : Nat) : Nat := evmAdd 0xad4506af99be27419341e1816ff351 (evmShr 0x84 (evmMul (odS0 x) (vTree x)))
def odS2 (x : Nat) : Nat := evmAdd 0xaf566247c05753b42892f77b67a6b7c6 (evmShr 0x7a (evmMul (odS1 x) (vTree x)))

theorem odTree_layers (x : Nat) :
    odTree x = evmAdd 0x270a522f2b285a8374bfa62ed11c30f1 (evmShr 0x82 (evmMul (odS2 x) (vTree x))) :=
  rfl

theorem odS0_lt {x : Nat} (hv : vTree x < 2 ^ 120) : odS0 x < 2 ^ 121 := by
  have := (stage_bounds (c := 0xc926ddbecdeeb42e68cd16db7da8c1) (prev := 0xdc07aff8276bde9a361278df6a10)
    (v := vTree x) (P := 2 ^ 112) (V := 2 ^ 120) (sh := 0x7e) (by norm_num) hv (by norm_num)
    (by norm_num) (by rw [pvd 112 120 126 106 (by norm_num)]; norm_num)).2
  rw [pvd 112 120 126 106 (by norm_num)] at this; unfold odS0; omega

theorem odS1_lt {x : Nat} (hv : vTree x < 2 ^ 120) : odS1 x < 2 ^ 121 := by
  have := (stage_bounds (c := 0xad4506af99be27419341e1816ff351) (prev := odS0 x) (v := vTree x)
    (P := 2 ^ 121) (V := 2 ^ 120) (sh := 0x84) (odS0_lt hv) hv (by norm_num) (by norm_num)
    (by rw [pvd 121 120 132 109 (by norm_num)]; norm_num)).2
  rw [pvd 121 120 132 109 (by norm_num)] at this; unfold odS1; omega

theorem odS2_lt {x : Nat} (hv : vTree x < 2 ^ 120) : odS2 x < 2 ^ 129 := by
  have := (stage_bounds (c := 0xaf566247c05753b42892f77b67a6b7c6) (prev := odS1 x) (v := vTree x)
    (P := 2 ^ 121) (V := 2 ^ 120) (sh := 0x7a) (odS1_lt hv) hv (by norm_num) (by norm_num)
    (by rw [pvd 121 120 122 119 (by norm_num)]; norm_num)).2
  rw [pvd 121 120 122 119 (by norm_num)] at this; unfold odS2; omega

/-! ## Composed Lipschitz bounds -/

/-- **Even accumulator near-constancy.** Under a squared-argument gap `|v2 − v1| ≤ W` the even
accumulator changes by at most `DEv = 42618413185`. -/
theorem evTree_lip {x1 x2 : Nat} (hv1 : vTree x1 < 2 ^ 120) (hv2 : vTree x2 < 2 ^ 120)
    (hg1 : vTree x1 ≤ vTree x2 + Wstep) (hg2 : vTree x2 ≤ vTree x1 + Wstep) :
    dist_le (evTree x1) (evTree x2) 42618413185 := by
  -- monic leading stage: distance exactly the argument gap
  have d0 : dist_le (evS0 x1) (evS0 x2) Wstep :=
    evLead_lip (c := 0xb9aacfacf3c10b378435f8e22adf48500e) (W := Wstep) (by norm_num) hv1 hv2 hg1 hg2
  -- stage 1
  have d1 : dist_le (evS1 x1) (evS1 x2) 941485 := by
    have h := stage_lip_dist (c := 0x9a036222841f47c6ed6fc3f7602053)
      (P := 0xb9aacfacf3c10b378435f8e22adf48500e + 2 ^ 120) (V := 2 ^ 120) (sh := 0x95) (W := Wstep)
      (Dprev := Wstep) (le_of_lt (evS0_lt hv1)) (le_of_lt (evS0_lt hv2)) hv1 hv2 hg1 hg2 d0
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have he : ((0xb9aacfacf3c10b378435f8e22adf48500e + 2 ^ 120) * Wstep + 2 ^ 120 * Wstep) / 2 ^ 0x95 + 1 =
        941485 := by unfold Wstep; decide
    rw [he] at h; exact h
  -- stage 2
  have d2 : dist_le (evS2 x1) (evS2 x2) 2658573678 := by
    have h := stage_lip_dist (c := 0x9064d9657e9a21fc16bb69331c5c3057) (P := 2 ^ 121) (V := 2 ^ 120)
      (sh := 0x7b) (W := Wstep)
      (Dprev := 941485) (le_of_lt (evS1_lt hv1)) (le_of_lt (evS1_lt hv2)) hv1 hv2 hg1 hg2 d1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have he : (2 ^ 121 * Wstep + 2 ^ 120 * 941485) / 2 ^ 0x7b + 1 = 2658573678 := by
      unfold Wstep; decide
    rw [he] at h; exact h
  -- stage 3
  have d3 : dist_le (evS3 x1) (evS3 x2) 10639016494 := by
    have h := stage_lip_dist (c := 0x93f11e650dd6c64b96ce79065cdf809e) (P := 2 ^ 129) (V := 2 ^ 120)
      (sh := 0x81) (W := Wstep)
      (Dprev := 2658573678) (le_of_lt (evS2_lt hv1)) (le_of_lt (evS2_lt hv2)) hv1 hv2 hg1 hg2 d2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have he : (2 ^ 129 * Wstep + 2 ^ 120 * 2658573678) / 2 ^ 0x81 + 1 = 10639016494 := by
      unfold Wstep; decide
    rw [he] at h; exact h
  -- final stage
  have hfin := stage_lip_dist (c := 0x4e14a45e5650b506e97f4c5da23861e2) (P := 2 ^ 129) (V := 2 ^ 120)
    (sh := 0x7f) (W := Wstep)
    (Dprev := 10639016494) (le_of_lt (evS3_lt hv1)) (le_of_lt (evS3_lt hv2)) hv1 hv2 hg1 hg2 d3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he : (2 ^ 129 * Wstep + 2 ^ 120 * 10639016494) / 2 ^ 0x7f + 1 = 42618413185 := by
    unfold Wstep; decide
  rw [he] at hfin
  rw [evTree_layers, evTree_layers]; exact hfin

/-- **Odd accumulator near-constancy.** Under a squared-argument gap `|v2 − v1| ≤ W` the odd
accumulator changes by at most `DOd = 5322105549`. -/
theorem odTree_lip {x1 x2 : Nat} (hv1 : vTree x1 < 2 ^ 120) (hv2 : vTree x2 < 2 ^ 120)
    (hg1 : vTree x1 ≤ vTree x2 + Wstep) (hg2 : vTree x2 ≤ vTree x1 + Wstep) :
    dist_le (odTree x1) (odTree x2) 5322105549 := by
  -- stage 0: prev is the constant leading coefficient (distance 0)
  have d0 : dist_le (odS0 x1) (odS0 x2) 649038 := by
    have h := stage_lip_dist (c := 0xc926ddbecdeeb42e68cd16db7da8c1) (P := 2 ^ 112) (V := 2 ^ 120)
      (sh := 0x7e) (W := Wstep)
      (Dprev := 0) (prev1 := 0xdc07aff8276bde9a361278df6a10) (prev2 := 0xdc07aff8276bde9a361278df6a10)
      (by norm_num) (by norm_num) hv1 hv2 hg1 hg2 (odLead_const _) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
    have he : (2 ^ 112 * Wstep + 2 ^ 120 * 0) / 2 ^ 0x7e + 1 = 649038 := by unfold Wstep; decide
    rw [he] at h; exact h
  have d1 : dist_le (odS1 x1) (odS1 x2) 5192456 := by
    have h := stage_lip_dist (c := 0xad4506af99be27419341e1816ff351) (P := 2 ^ 121) (V := 2 ^ 120)
      (sh := 0x84) (W := Wstep)
      (Dprev := 649038) (le_of_lt (odS0_lt hv1)) (le_of_lt (odS0_lt hv2)) hv1 hv2 hg1 hg2 d0
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have he : (2 ^ 121 * Wstep + 2 ^ 120 * 649038) / 2 ^ 0x84 + 1 = 5192456 := by unfold Wstep; decide
    rw [he] at h; exact h
  have d2 : dist_le (odS2 x1) (odS2 x2) 5318210098 := by
    have h := stage_lip_dist (c := 0xaf566247c05753b42892f77b67a6b7c6) (P := 2 ^ 121) (V := 2 ^ 120)
      (sh := 0x7a) (W := Wstep)
      (Dprev := 5192456) (le_of_lt (odS1_lt hv1)) (le_of_lt (odS1_lt hv2)) hv1 hv2 hg1 hg2 d1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have he : (2 ^ 121 * Wstep + 2 ^ 120 * 5192456) / 2 ^ 0x7a + 1 = 5318210098 := by
      unfold Wstep; decide
    rw [he] at h; exact h
  have hfin := stage_lip_dist (c := 0x270a522f2b285a8374bfa62ed11c30f1) (P := 2 ^ 129) (V := 2 ^ 120)
    (sh := 0x82) (W := Wstep)
    (Dprev := 5318210098) (le_of_lt (odS2_lt hv1)) (le_of_lt (odS2_lt hv2)) hv1 hv2 hg1 hg2 d2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he : (2 ^ 129 * Wstep + 2 ^ 120 * 5318210098) / 2 ^ 0x82 + 1 = 5322105549 := by
    unfold Wstep; decide
  rw [he] at hfin
  rw [odTree_layers, odTree_layers]; exact hfin

end ExpYul

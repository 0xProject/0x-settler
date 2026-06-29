import ExpProof.Mono.Stages

/-!
# A composed Lipschitz bound for the even/odd Horner accumulators

Adjacent same-octave inputs move the reduced argument `t` by the small step `G ≤ t2 − t1 ≤ G + 1`,
hence move `v = ⌊t²/2^128⌋` by at most `W = G + 1`. The even/odd accumulators `Ev`/`Od` are then
nearly constant: each Horner stage `evmAdd c (evmShr sh (evmMul prev v))` changes by a bounded
amount under a bounded change of `v` (and of the incoming accumulator `prev`), and the five/four
stages compose to the constants `DEv`/`DOd`.

The single-stage bound rests on a floor-difference fact: shifting two operands right by the same
amount changes their difference by at most the shifted difference plus one. Everything is stated
over opaque words so the deep accumulator trees are never forced into whnf.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

/-- The per-step reduced-argument gap `G = ⌊K27 / 2^107⌋`. -/
def Gstep : Nat := 340282366920

/-- Floored sum bound: `⌊(b + n)/d⌋ ≤ ⌊b/d⌋ + ⌊n/d⌋ + 1`. The two truncations of the split lose at
most one unit jointly. -/
theorem add_div_le_add {b n d : Nat} (hd : 0 < d) :
    (b + n) / d ≤ b / d + n / d + 1 := by
  have m1 := Nat.mod_lt b hd
  have m2 := Nat.mod_lt n hd
  have hb := Nat.div_add_mod b d
  have hn := Nat.div_add_mod n d
  have key : d * ((b + n) / d) < d * (b / d + n / d + 2) := by
    have hbn : b + n < d * (b / d) + d + (d * (n / d) + d) := by omega
    have e : d * (b / d + n / d + 2) = d * (b / d) + d * (n / d) + d + d := by ring
    have hle : d * ((b + n) / d) ≤ b + n := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
    omega
  have hlt := Nat.lt_of_mul_lt_mul_left key
  omega

/-- One Horner stage's Lipschitz bound. With `prev_i ≤ P`, `v_i ≤ 2^126`, the products fitting a
word, `|v2 − v1| ≤ W` and `|prev2 − prev1| ≤ Dprev`, the stage output `evmAdd c (evmShr sh (evmMul
prev v))` moves by at most `⌊(P·W + 2^126·Dprev)/2^sh⌋ + 1`. Stated as a two-sided `Nat` distance
over opaque words. -/
theorem stage_lip {c prev1 prev2 v1 v2 P Dprev W sh : Nat}
    (hp1 : prev1 ≤ P) (hp2 : prev2 ≤ P) (hv1 : v1 < 2 ^ 126) (hv2 : v2 < 2 ^ 126)
    (hvg1 : v1 ≤ v2 + W) (hvg2 : v2 ≤ v1 + W)
    (hpg1 : prev1 ≤ prev2 + Dprev) (hpg2 : prev2 ≤ prev1 + Dprev)
    (hPV : P * 2 ^ 126 < 2 ^ 256) (hsh : sh < 256)
    (hsum1 : c + P * 2 ^ 126 / 2 ^ sh < 2 ^ 256) :
    evmAdd c (evmShr sh (evmMul prev1 v1)) ≤
        evmAdd c (evmShr sh (evmMul prev2 v2)) + ((P * W + 2 ^ 126 * Dprev) / 2 ^ sh + 1) ∧
      evmAdd c (evmShr sh (evmMul prev2 v2)) ≤
        evmAdd c (evmShr sh (evmMul prev1 v1)) + ((P * W + 2 ^ 126 * Dprev) / 2 ^ sh + 1) := by
  -- products are exact (fit a word) and the stage adds are exact (no overflow)
  have hpvbnd : ∀ p v : Nat, p ≤ P → v < 2 ^ 126 → p * v < 2 ^ 256 ∧ p * v ≤ P * 2 ^ 126 := by
    intro p v hp hv
    have h1 : p * v ≤ P * v := Nat.mul_le_mul_right _ hp
    have h2 : P * v ≤ P * 2 ^ 126 := Nat.mul_le_mul_left _ (le_of_lt hv)
    exact ⟨by omega, by omega⟩
  obtain ⟨hpv1lt, hpv1le⟩ := hpvbnd prev1 v1 hp1 hv1
  obtain ⟨hpv2lt, hpv2le⟩ := hpvbnd prev2 v2 hp2 hv2
  have hm1 : evmMul prev1 v1 = prev1 * v1 :=
    evmMul_eq_nat (by omega) (by omega) hpv1lt
  have hm2 : evmMul prev2 v2 = prev2 * v2 :=
    evmMul_eq_nat (by omega) (by omega) hpv2lt
  have hs1 : evmShr sh (evmMul prev1 v1) = prev1 * v1 / 2 ^ sh := by
    rw [hm1]; exact evmShr_eq_div hsh hpv1lt
  have hs2 : evmShr sh (evmMul prev2 v2) = prev2 * v2 / 2 ^ sh := by
    rw [hm2]; exact evmShr_eq_div hsh hpv2lt
  have hsh1 : prev1 * v1 / 2 ^ sh ≤ P * 2 ^ 126 / 2 ^ sh := Nat.div_le_div_right hpv1le
  have hsh2 : prev2 * v2 / 2 ^ sh ≤ P * 2 ^ 126 / 2 ^ sh := Nat.div_le_div_right hpv2le
  have he1 : evmAdd c (evmShr sh (evmMul prev1 v1)) = c + prev1 * v1 / 2 ^ sh := by
    rw [hs1, evmAdd_eq_nat (by omega) (by omega) (by omega)]
  have he2 : evmAdd c (evmShr sh (evmMul prev2 v2)) = c + prev2 * v2 / 2 ^ sh := by
    rw [hs2, evmAdd_eq_nat (by omega) (by omega) (by omega)]
  rw [he1, he2]
  -- bound the product difference: |prev2·v2 − prev1·v1| ≤ P·W + 2^126·Dprev
  have hprodbound : ∀ pa pb va vb : Nat, pa ≤ P → pb ≤ P → va < 2 ^ 126 → vb < 2 ^ 126 →
      va ≤ vb + W → pa ≤ pb + Dprev →
      pa * va ≤ pb * vb + (P * W + 2 ^ 126 * Dprev) := by
    intro pa pb va vb hpa hpb hva hvb hvgap hpgap
    -- pa·va ≤ pa·(vb + W) = pa·vb + pa·W ≤ pa·vb + P·W
    -- pa·vb ≤ (pb + Dprev)·vb = pb·vb + Dprev·vb ≤ pb·vb + Dprev·2^126
    have t1 : pa * va ≤ pa * (vb + W) := Nat.mul_le_mul_left _ hvgap
    have t2 : pa * (vb + W) = pa * vb + pa * W := by ring
    have t3 : pa * W ≤ P * W := Nat.mul_le_mul_right _ hpa
    have t4 : pa * vb ≤ (pb + Dprev) * vb := Nat.mul_le_mul_right _ hpgap
    have t5 : (pb + Dprev) * vb = pb * vb + Dprev * vb := by ring
    have t6 : Dprev * vb ≤ Dprev * 2 ^ 126 := Nat.mul_le_mul_left _ (le_of_lt hvb)
    have t7 : Dprev * 2 ^ 126 = 2 ^ 126 * Dprev := Nat.mul_comm _ _
    omega
  have hpd12 := hprodbound prev1 prev2 v1 v2 hp1 hp2 hv1 hv2 hvg1 hpg1
  have hpd21 := hprodbound prev2 prev1 v2 v1 hp2 hp1 hv2 hv1 hvg2 hpg2
  have hsh0 : 0 < 2 ^ sh := Nat.two_pow_pos sh
  set B := (P * W + 2 ^ 126 * Dprev) / 2 ^ sh with hB
  -- one-sided floor bound: `prev1·v1/2^sh ≤ prev2·v2/2^sh + (B + 1)`
  have hone : ∀ pa va pb vb : Nat, pa * va ≤ pb * vb + (P * W + 2 ^ 126 * Dprev) →
      pa * va / 2 ^ sh ≤ pb * vb / 2 ^ sh + (B + 1) := by
    intro pa va pb vb hbnd
    -- `pa·va/2^sh ≤ (pb·vb + N)/2^sh ≤ pb·vb/2^sh + N/2^sh + 1`, and `N/2^sh = B`.
    have s1 : pa * va / 2 ^ sh ≤ (pb * vb + (P * W + 2 ^ 126 * Dprev)) / 2 ^ sh :=
      Nat.div_le_div_right hbnd
    have s2 := add_div_le_add (b := pb * vb) (n := P * W + 2 ^ 126 * Dprev) hsh0
    rw [← hB] at s2
    omega
  have h12 := hone prev1 v1 prev2 v2 hpd12
  have h21 := hone prev2 v2 prev1 v1 hpd21
  omega

end ExpYul

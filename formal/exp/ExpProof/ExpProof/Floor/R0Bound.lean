import ExpProof.Floor.Fold
import ExpProof.Floor.TBound
import ExpProof.Mono.Quot
import ExpProof.Spec.RealExp
import Common.Foundation.ExpSum
import Common.Seam.RealExpBridge
import Mathlib.Data.Complex.ExponentialBounds

/-!
# Discharging the runtime `r0` bound

The public floor brackets need the Q126 quotient `r0Tree x` bracketed against the target
`E = 10¹⁸·exp(int256 x / 10²⁷)` across the octave shift `2^(108 − k)`. This file builds two
ingredients of that discharge:

* the **Horner-truncation bridge** for the even/odd accumulators — the runtime `evTree x`/`odTree x`,
  which truncate each Horner `>>` stage, bracket the exact integer polynomials `evNumV (vTree x)`
  (degree 5, cleared scale `2^528`) and `odNumV (vTree x)` (degree 4, cleared scale `2^510`): the
  monic leading stage is an exact add, and the four lossy stages' floor losses telescope with
  shrinking amplification (each stage shift exceeds `120 = ⌈log₂ v⌉`), leaving widths
  `283678831804417·2^480 ≈ 1.0079·2^528` and `1075052609·2^480 ≈ 1.0013·2^510`;
* the self-contained **below-clamp bound** — below the clamp boundary the target is under one output
  unit — directly from a `Real.exp` rational bound.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-! ## The Horner accumulators bracket the exact polynomials

Each runtime Horner stage `evmAdd c (evmShr sh (evmMul prev v))` is the integer floor
`c + ⌊prev·v / 2^sh⌋`; the floor loss `< 1` at scale `2^sh`. The *fractional* telescope tracks the
exact deficit width as `Wnum·2^p` (a dyadic rational `Wnum/2^(cum−p)` at the cumulative scale
`2^cum`). Across a stage with shift `s ≥ 120` the carried width is attenuated by
`v/2^s ≤ 2^(120−s) < 1`, so the width evolves as `W' = W·2^(120−s) + 1` and stays near one unit. -/

theorem stage_exact {c prev v sh : Nat} (hprev : prev < 2^256) (hvw : v < 2^256)
    (hpv : prev * v < 2 ^ 256) (hsh : sh < 256)
    (hc : c < 2 ^ 256) (hsum : c + prev * v / 2 ^ sh < 2 ^ 256) :
    2 ^ sh * (evmAdd c (evmShr sh (evmMul prev v)) - c) ≤ prev * v ∧
      prev * v < 2 ^ sh * (evmAdd c (evmShr sh (evmMul prev v)) - c) + 2 ^ sh := by
  have hmul : evmMul prev v = prev * v := evmMul_eq_nat hprev hvw hpv
  have hshr : evmShr sh (evmMul prev v) = prev * v / 2 ^ sh := by rw [hmul]; exact evmShr_eq_div hsh hpv
  have hshr_lt : prev * v / 2 ^ sh < 2 ^ 256 := lt_of_le_of_lt (Nat.div_le_self _ _) hpv
  rw [hshr, evmAdd_eq_nat hc hshr_lt hsum, Nat.add_sub_cancel_left]
  have hpos : 0 < 2 ^ sh := Nat.two_pow_pos sh
  have hdm := Nat.div_add_mod (prev * v) (2 ^ sh)
  have hmod := Nat.mod_lt (prev * v) hpos
  generalize prev * v / 2 ^ sh = q at *
  generalize prev * v % 2 ^ sh = r at *
  omega

/-- The state is `2^cum·e ≤ E < 2^cum·e + Wnum·2^p` with `p ≤ cum` (the width exponent). One stage
with shift `s ≥ 120` (constant `A`, `e1 = A + ⌊e0·v/2^s⌋`, `v < 2^120`) produces the new width
`Wnum' = Wnum + 2^(cum+s−p−120)` at exponent `p' = p + 120` and scale `cum' = cum + s`. -/
theorem tele_step_frac (e0 e1 v A cum s p Wnum E0 : Nat)
    (hv : v < 2^120) (hs : 120 ≤ s) (hAe1 : A ≤ e1) (hpcum : p + 120 ≤ cum + s)
    (hb0lo : 2^cum * e0 ≤ E0) (hb0hi : E0 < 2^cum * e0 + Wnum * 2^p)
    (hslo : 2^s * (e1 - A) ≤ e0 * v) (hshi : e0 * v < 2^s * (e1 - A) + 2^s) :
    2^(cum+s) * e1 ≤ A * 2^(cum+s) + E0 * v ∧
      A * 2^(cum+s) + E0 * v <
        2^(cum+s) * e1 + (Wnum + 2^(cum+s-(p+120))) * 2^(p+120) := by
  -- factor the relevant power identities, then abstract every `2^…` to an opaque var
  have hsplit : (2:Nat)^(cum+s) = 2^cum * 2^s := by rw [Nat.pow_add]
  -- key: 2^cum · 2^s = 2^(p+120) · 2^(cum+s-(p+120)) = 2^p · 2^120 · G
  have hG : (2:Nat)^cum * 2^s = (2^p * 2^120) * 2^(cum+s-(p+120)) := by
    rw [show (2:Nat)^p * 2^120 = 2^(p+120) from by rw [Nat.pow_add],
      ← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
  have hPP120 : (2:Nat)^(p+120) = 2^p * 2^120 := by rw [Nat.pow_add]
  have hP120 : (0:Nat) < 2^120 := Nat.two_pow_pos _
  have hPcum : (0:Nat) < 2^cum := Nat.two_pow_pos _
  set d := e1 - A with hd
  have he1eq : e1 = A + d := by omega
  -- abstract powers
  set P := (2:Nat)^cum with hPdef
  set Q := (2:Nat)^s with hQdef
  set R := (2:Nat)^p with hRdef
  set H := (2:Nat)^120 with hHdef
  set G := (2:Nat)^(cum+s-(p+120)) with hGdef
  -- collected facts in abstract form
  rw [hsplit, he1eq]
  rw [show (2:Nat)^(p+120) = R * H from hPP120]
  have hPQ : P * Q = (R * H) * G := hG
  have hvH : v ≤ H := le_of_lt hv
  have hRpos : 0 < R := by rw [hRdef]; exact Nat.two_pow_pos _
  have hHpos : 0 < H := by rw [hHdef]; exact Nat.two_pow_pos _
  have hGpos : 0 < G := by rw [hGdef]; exact Nat.two_pow_pos _
  clear_value P Q R H G
  have hRHpos : 0 < R * H := Nat.mul_pos hRpos hHpos
  -- lower bound
  have key_lo : P * Q * d ≤ E0 * v := by
    calc P * Q * d = P * (Q * d) := by ring
      _ ≤ P * (e0 * v) := by gcongr
      _ = (P * e0) * v := by ring
      _ ≤ E0 * v := by gcongr
  -- upper bound, an explicit chain in the abstract powers
  have key_hi : E0 * v < P * Q * d + (Wnum + G) * (R * H) := by
    rcases Nat.eq_zero_or_pos v with hv0 | hv0
    · subst hv0
      have hpos : (0:Nat) < (Wnum + G) * (R * H) :=
        Nat.mul_pos (by omega) hRHpos
      have : E0 * 0 < P * Q * d + (Wnum + G) * (R * H) := by
        rw [Nat.mul_zero]; exact Nat.lt_of_lt_of_le hpos (Nat.le_add_left _ _)
      simpa using this
    have h1 : E0 * v < (P * e0 + Wnum * R) * v := (Nat.mul_lt_mul_right hv0).mpr hb0hi
    have h3 : P * (e0 * v) < P * (Q * d + Q) := (Nat.mul_lt_mul_left hPcum).mpr hshi
    have hcarry : Wnum * R * v ≤ Wnum * (R * H) := by
      calc Wnum * R * v ≤ Wnum * R * H := by gcongr
        _ = Wnum * (R * H) := by ring
    calc E0 * v < (P * e0 + Wnum * R) * v := h1
      _ = P * (e0 * v) + Wnum * R * v := by ring
      _ < P * (Q * d + Q) + Wnum * (R * H) := by
            exact Nat.add_lt_add_of_lt_of_le h3 hcarry
      _ = P * Q * d + (R * H) * G + Wnum * (R * H) := by rw [← hPQ]; ring
      _ = P * Q * d + (Wnum + G) * (R * H) := by ring
  refine ⟨?_, ?_⟩
  · calc P * Q * (A + d) = A * (P * Q) + P * Q * d := by ring
      _ ≤ A * (P * Q) + E0 * v := by exact Nat.add_le_add_left key_lo _
  · calc A * (P * Q) + E0 * v < A * (P * Q) + (P * Q * d + (Wnum + G) * (R * H)) :=
            Nat.add_lt_add_left key_hi _
      _ = P * Q * (A + d) + (Wnum + G) * (R * H) := by ring

/-- One runtime Horner stage propagates a dyadic-fraction deficit width `Wnum·2^p` into
`(Wnum + 2^(cum+sh−p−120))·2^(p+120)` (the carried width is attenuated by `v/2^sh ≤ 2^(120−sh) < 1`).
Consumes `tele_step_frac`; the word-arithmetic side conditions are discharged from the raw product
bound `prev·v < 2^256` and the coefficient cap `c < 2^160`. -/
theorem horner_stage_frac (c prev v cum sh p Wnum Eprev : Nat)
    (hv : v < 2^120) (hs : 120 ≤ sh) (hsh256 : sh < 256)
    (hprev256 : prev < 2^256) (hpv : prev * v < 2^256) (hclt : c < 2^160)
    (hpcum : p + 120 ≤ cum + sh)
    (hElo : 2^cum * prev ≤ Eprev) (hEhi : Eprev < 2^cum * prev + Wnum * 2^p) :
    2^(cum+sh) * (evmAdd c (evmShr sh (evmMul prev v))) ≤ c * 2^(cum+sh) + Eprev * v ∧
      c * 2^(cum+sh) + Eprev * v <
        2^(cum+sh) * (evmAdd c (evmShr sh (evmMul prev v))) +
          (Wnum + 2^(cum+sh-(p+120))) * 2^(p+120) := by
  have hv256 : v < 2^256 := by have : (2:Nat)^120 < 2^256 := by norm_num
                               omega
  have hc256 : c < 2^256 := by have : (2:Nat)^160 < 2^256 := by norm_num
                               omega
  -- the truncated stage term is below `2^136`: the product is a word and the shift is ≥ 120
  have hterm : prev * v / 2 ^ sh < 2 ^ 136 := by
    have h1 : prev * v / 2 ^ sh ≤ prev * v / 2 ^ 120 :=
      Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) hs) (Nat.two_pow_pos _)
    have h2 : prev * v / 2 ^ 120 < 2 ^ 136 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
      calc prev * v < 2 ^ 256 := hpv
        _ = 2 ^ 136 * 2 ^ 120 := by rw [← Nat.pow_add]
    omega
  have hsum' : c + prev * v / 2 ^ sh < 2 ^ 256 := by
    have : (2:Nat)^160 + 2^136 < 2^256 := by norm_num
    omega
  have hst := stage_exact hprev256 hv256 hpv hsh256 hc256 hsum'
  set ev1 := evmAdd c (evmShr sh (evmMul prev v)) with hev1
  have hge : c ≤ ev1 := by
    rw [hev1, evmAdd_eq_nat hc256 (by exact evmShr_lt _ _) (by
      have hmul : evmMul prev v = prev * v := evmMul_eq_nat hprev256 hv256 hpv
      have : evmShr sh (evmMul prev v) = prev*v/2^sh := by rw [hmul]; exact evmShr_eq_div (by omega) hpv
      rw [this]; omega)]
    omega
  exact tele_step_frac prev ev1 v c cum sh p Wnum Eprev hv hs hge hpcum hElo hEhi hst.1 hst.2

/-! ## The even accumulator

The monic leading stage `ev0 = A4 + v` is an exact add (width `1·2^0`); the four `mul/shr` stages
(shifts `0x95, 0x7b, 0x81, 0x7f`, cumulative `149, 272, 401, 528`) telescope the width to
`283678831804417·2^480 ≈ 1.0079·2^528`. -/

/-- Exact integer even-Horner accumulator (degree-5 monic in `v`, cleared scale `2^528`). -/
def evNumV (v : Nat) : Nat :=
  let e0 := 0xb9aacfacf3c10b378435f8e22adf48500e + v
  let e1 := 0x9a036222841f47c6ed6fc3f7602053 * 2^149 + e0 * v
  let e2 := 0x9064d9657e9a21fc16bb69331c5c3057 * 2^272 + e1 * v
  let e3 := 0x93f11e650dd6c64b96ce79065cdf809e * 2^401 + e2 * v
  0x4e14a45e5650b506e97f4c5da23861e2 * 2^528 + e3 * v

theorem evTree_bracket {x : Nat} (hv : vTree x < 2 ^ 120) :
    2^528 * evTree x ≤ evNumV (vTree x) ∧
      evNumV (vTree x) < 2^528 * evTree x + 283678831804417 * 2^480 := by
  have hev : evTree x =
      evmAdd 0x4e14a45e5650b506e97f4c5da23861e2 (evmShr 0x7f (evmMul
      (evmAdd 0x93f11e650dd6c64b96ce79065cdf809e (evmShr 0x81 (evmMul
      (evmAdd 0x9064d9657e9a21fc16bb69331c5c3057 (evmShr 0x7b (evmMul
      (evmAdd 0x9a036222841f47c6ed6fc3f7602053 (evmShr 0x95 (evmMul
      (evmAdd 0xb9aacfacf3c10b378435f8e22adf48500e (vTree x)) (vTree x)))) (vTree x)))) (vTree x)))) (vTree x))) := rfl
  set v := vTree x with hvdef
  -- stage 0: the monic add is exact; width 1·2^0
  have he0eq : evmAdd 0xb9aacfacf3c10b378435f8e22adf48500e v =
      0xb9aacfacf3c10b378435f8e22adf48500e + v :=
    evmAdd_eq_nat (by norm_num) (by have : (2:Nat)^120 < 2^256 := by norm_num
                                    omega)
      (by have : (0xb9aacfacf3c10b378435f8e22adf48500e : Nat) + 2^120 < 2^256 := by norm_num
          omega)
  set e0 := evmAdd 0xb9aacfacf3c10b378435f8e22adf48500e v with he0
  have he0lt : e0 < 0xb9aacfacf3c10b378435f8e22adf48500e + 2 ^ 120 := ev0_lt hv
  have hE0lo : 2^0 * e0 ≤ 0xb9aacfacf3c10b378435f8e22adf48500e + v := by
    rw [he0eq, pow_zero, one_mul]
  have hE0hi : 0xb9aacfacf3c10b378435f8e22adf48500e + v < 2^0 * e0 + 1 * 2^0 := by
    rw [he0eq, pow_zero, one_mul, mul_one]
    omega
  -- stage 1: cum 0 -> 149, sh=149; p 0 -> 120; Wnum 1 -> 536870913
  have s1 := horner_stage_frac 0x9a036222841f47c6ed6fc3f7602053 e0 v 0 0x95 0 1
    (0xb9aacfacf3c10b378435f8e22adf48500e + v) hv (by norm_num) (by norm_num)
    (by have : (0xb9aacfacf3c10b378435f8e22adf48500e : Nat) + 2^120 < 2^256 := by norm_num
        omega)
    (by calc e0 * v < (0xb9aacfacf3c10b378435f8e22adf48500e + 2^120) * 2^120 :=
              Nat.mul_lt_mul'' he0lt hv
          _ < 2^256 := by norm_num)
    (by norm_num) (by norm_num) hE0lo hE0hi
  rw [show (0:Nat)+0x95-(0+120) = 29 from by norm_num, show (1:Nat)+2^29 = 536870913 from by norm_num,
    show (0:Nat)+120 = 120 from by norm_num, show (0:Nat)+0x95 = 149 from by norm_num] at s1
  set e1 := evmAdd 0x9a036222841f47c6ed6fc3f7602053 (evmShr 0x95 (evmMul e0 v)) with he1
  have he1lt : e1 < 2^121 := by
    have := (stage_bounds (c := 0x9a036222841f47c6ed6fc3f7602053) (prev := e0) (v := v)
      (P := 0xb9aacfacf3c10b378435f8e22adf48500e + 2 ^ 120) (V := 2 ^ 120) (sh := 0x95) he0lt hv
      (by norm_num) (by norm_num) (by norm_num)).2
    have hcap : (0x9a036222841f47c6ed6fc3f7602053 : Nat) +
        (0xb9aacfacf3c10b378435f8e22adf48500e + 2 ^ 120) * 2 ^ 120 / 2 ^ 0x95 < 2 ^ 121 := by
      norm_num
    omega
  -- stage 2: cum 149 -> 272, sh=123; p 120 -> 240; Wnum 536870913 -> 4831838209
  have s2 := horner_stage_frac 0x9064d9657e9a21fc16bb69331c5c3057 e1 v 149 0x7b 120 536870913
    (0x9a036222841f47c6ed6fc3f7602053 * 2^149 + (0xb9aacfacf3c10b378435f8e22adf48500e + v) * v)
    hv (by norm_num) (by norm_num)
    (by have : (2:Nat)^121 < 2^256 := by norm_num
        omega)
    (by calc e1 * v < 2^121 * 2^120 := Nat.mul_lt_mul'' he1lt hv
          _ < 2^256 := by norm_num)
    (by norm_num) (by norm_num) s1.1 s1.2
  rw [show (149:Nat)+0x7b-(120+120) = 32 from by norm_num,
    show (536870913:Nat)+2^32 = 4831838209 from by norm_num,
    show (120:Nat)+120 = 240 from by norm_num, show (149:Nat)+0x7b = 272 from by norm_num] at s2
  set e2 := evmAdd 0x9064d9657e9a21fc16bb69331c5c3057 (evmShr 0x7b (evmMul e1 v)) with he2
  have he2lt : e2 < 2^129 := by
    have := (stage_bounds (c := 0x9064d9657e9a21fc16bb69331c5c3057) (prev := e1) (v := v)
      (P := 2^121) (V := 2^120) (sh := 0x7b) he1lt hv (by norm_num) (by norm_num)
      (by rw [pvd 121 120 123 118 (by norm_num)]; norm_num)).2
    rw [pvd 121 120 123 118 (by norm_num)] at this; omega
  -- stage 3: cum 272 -> 401, sh=129; p 240 -> 360; Wnum 4831838209 -> 2203855093761
  have s3 := horner_stage_frac 0x93f11e650dd6c64b96ce79065cdf809e e2 v 272 0x81 240 4831838209
    (0x9064d9657e9a21fc16bb69331c5c3057 * 2^272 +
      (0x9a036222841f47c6ed6fc3f7602053 * 2^149 + (0xb9aacfacf3c10b378435f8e22adf48500e + v) * v) * v)
    hv (by norm_num) (by norm_num)
    (by have : (2:Nat)^129 < 2^256 := by norm_num
        omega)
    (by calc e2 * v < 2^129 * 2^120 := Nat.mul_lt_mul'' he2lt hv
          _ < 2^256 := by norm_num)
    (by norm_num) (by norm_num) s2.1 s2.2
  rw [show (272:Nat)+0x81-(240+120) = 41 from by norm_num,
    show (4831838209:Nat)+2^41 = 2203855093761 from by norm_num,
    show (240:Nat)+120 = 360 from by norm_num, show (272:Nat)+0x81 = 401 from by norm_num] at s3
  set e3 := evmAdd 0x93f11e650dd6c64b96ce79065cdf809e (evmShr 0x81 (evmMul e2 v)) with he3
  have he3lt : e3 < 2^129 := by
    have := (stage_bounds (c := 0x93f11e650dd6c64b96ce79065cdf809e) (prev := e2) (v := v)
      (P := 2^129) (V := 2^120) (sh := 0x81) he2lt hv (by norm_num) (by norm_num)
      (by rw [pvd 129 120 129 120 (by norm_num)]; norm_num)).2
    rw [pvd 129 120 129 120 (by norm_num)] at this; omega
  -- stage 4: cum 401 -> 528, sh=127; p 360 -> 480; Wnum 2203855093761 -> 283678831804417
  have s4 := horner_stage_frac 0x4e14a45e5650b506e97f4c5da23861e2 e3 v 401 0x7f 360 2203855093761
    (0x93f11e650dd6c64b96ce79065cdf809e * 2^401 +
      (0x9064d9657e9a21fc16bb69331c5c3057 * 2^272 +
        (0x9a036222841f47c6ed6fc3f7602053 * 2^149 +
          (0xb9aacfacf3c10b378435f8e22adf48500e + v) * v) * v) * v)
    hv (by norm_num) (by norm_num)
    (by have : (2:Nat)^129 < 2^256 := by norm_num
        omega)
    (by calc e3 * v < 2^129 * 2^120 := Nat.mul_lt_mul'' he3lt hv
          _ < 2^256 := by norm_num)
    (by norm_num) (by norm_num) s3.1 s3.2
  rw [show (401:Nat)+0x7f-(360+120) = 48 from by norm_num,
    show (2203855093761:Nat)+2^48 = 283678831804417 from by norm_num,
    show (360:Nat)+120 = 480 from by norm_num, show (401:Nat)+0x7f = 528 from by norm_num] at s4
  -- assemble: evTree x = e4 (the stage-4 value), evNumV v = the cumulative E4.
  rw [hev]
  show 2^528 * evmAdd 0x4e14a45e5650b506e97f4c5da23861e2 (evmShr 0x7f (evmMul e3 v)) ≤ evNumV v ∧
    evNumV v < 2^528 * evmAdd 0x4e14a45e5650b506e97f4c5da23861e2 (evmShr 0x7f (evmMul e3 v)) +
      283678831804417 * 2^480
  unfold evNumV
  constructor
  · have := s4.1
    convert this using 2 <;> ring
  · have := s4.2
    convert this using 2 <;> ring


/-- info: 'ExpYul.evTree_bracket' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evTree_bracket

/-! ## The odd accumulator

The odd accumulator starts at the exact leading constant `B4` (scale `0`) and runs four mul/shr
stages (shifts `0x7e, 0x84, 0x7a, 0x82`, cumulative `126, 258, 380, 510`), telescoping the width to
`1075052609·2^480 ≈ 1.0013·2^510`. -/

/-- Exact integer odd-Horner accumulator (degree-4 in `v`, cleared scale `2^510`). -/
def odNumV (v : Nat) : Nat :=
  let o1 := 0xc926ddbecdeeb42e68cd16db7da8c1 * 2^126 + 0xdc07aff8276bde9a361278df6a10 * v
  let o2 := 0xad4506af99be27419341e1816ff351 * 2^258 + o1 * v
  let o3 := 0xaf566247c05753b42892f77b67a6b7c6 * 2^380 + o2 * v
  0x270a522f2b285a8374bfa62ed11c30f1 * 2^510 + o3 * v

theorem odTree_bracket {x : Nat} (hv : vTree x < 2 ^ 120) :
    2^510 * odTree x ≤ odNumV (vTree x) ∧
      odNumV (vTree x) < 2^510 * odTree x + 1075052609 * 2^480 := by
  have hod : odTree x =
      evmAdd 0x270a522f2b285a8374bfa62ed11c30f1 (evmShr 0x82 (evmMul
      (evmAdd 0xaf566247c05753b42892f77b67a6b7c6 (evmShr 0x7a (evmMul
      (evmAdd 0xad4506af99be27419341e1816ff351 (evmShr 0x84 (evmMul
      (evmAdd 0xc926ddbecdeeb42e68cd16db7da8c1 (evmShr 0x7e (evmMul
      0xdc07aff8276bde9a361278df6a10 (vTree x)))) (vTree x)))) (vTree x)))) (vTree x))) := rfl
  set v := vTree x with hvdef
  -- the leading constant is exact; track it as width 1·2^0 (B4 < B4 + 1)
  have hB4lo : 2^0 * 0xdc07aff8276bde9a361278df6a10 ≤ 0xdc07aff8276bde9a361278df6a10 := by norm_num
  have hB4hi : (0xdc07aff8276bde9a361278df6a10 : Nat) <
      2^0 * 0xdc07aff8276bde9a361278df6a10 + 1 * 2^0 := by norm_num
  -- stage 1: cum 0 -> 126, sh=126; p 0 -> 120; Wnum 1 -> 65
  have s1 := horner_stage_frac 0xc926ddbecdeeb42e68cd16db7da8c1
    0xdc07aff8276bde9a361278df6a10 v 0 0x7e 0 1
    0xdc07aff8276bde9a361278df6a10 hv (by norm_num) (by norm_num) (by norm_num)
    (by calc (0xdc07aff8276bde9a361278df6a10 : Nat) * v < 2^112 * 2^120 :=
              Nat.mul_lt_mul'' (by norm_num) hv
          _ < 2^256 := by norm_num)
    (by norm_num) (by norm_num) hB4lo hB4hi
  rw [show (0:Nat)+0x7e-(0+120) = 6 from by norm_num, show (1:Nat)+2^6 = 65 from by norm_num,
    show (0:Nat)+120 = 120 from by norm_num, show (0:Nat)+0x7e = 126 from by norm_num] at s1
  set o1 := evmAdd 0xc926ddbecdeeb42e68cd16db7da8c1
    (evmShr 0x7e (evmMul 0xdc07aff8276bde9a361278df6a10 v)) with ho1
  have ho1lt : o1 < 2^121 := by
    have := (stage_bounds (c := 0xc926ddbecdeeb42e68cd16db7da8c1)
      (prev := 0xdc07aff8276bde9a361278df6a10) (v := v)
      (P := 2^112) (V := 2^120) (sh := 0x7e) (by norm_num) hv (by norm_num) (by norm_num)
      (by rw [pvd 112 120 126 106 (by norm_num)]; norm_num)).2
    rw [pvd 112 120 126 106 (by norm_num)] at this; omega
  -- stage 2: cum 126 -> 258, sh=132; p 120 -> 240; Wnum 65 -> 262209
  have s2 := horner_stage_frac 0xad4506af99be27419341e1816ff351 o1 v 126 0x84 120 65
    (0xc926ddbecdeeb42e68cd16db7da8c1 * 2^126 + 0xdc07aff8276bde9a361278df6a10 * v) hv
    (by norm_num) (by norm_num)
    (by have : (2:Nat)^121 < 2^256 := by norm_num
        omega)
    (by calc o1 * v < 2^121 * 2^120 := Nat.mul_lt_mul'' ho1lt hv
          _ < 2^256 := by norm_num)
    (by norm_num) (by norm_num) s1.1 s1.2
  rw [show (126:Nat)+0x84-(120+120) = 18 from by norm_num, show (65:Nat)+2^18 = 262209 from by norm_num,
    show (120:Nat)+120 = 240 from by norm_num, show (126:Nat)+0x84 = 258 from by norm_num] at s2
  set o2 := evmAdd 0xad4506af99be27419341e1816ff351 (evmShr 0x84 (evmMul o1 v)) with ho2
  have ho2lt : o2 < 2^121 := by
    have := (stage_bounds (c := 0xad4506af99be27419341e1816ff351) (prev := o1) (v := v)
      (P := 2^121) (V := 2^120) (sh := 0x84) ho1lt hv (by norm_num) (by norm_num)
      (by rw [pvd 121 120 132 109 (by norm_num)]; norm_num)).2
    rw [pvd 121 120 132 109 (by norm_num)] at this; omega
  -- stage 3: cum 258 -> 380, sh=122; p 240 -> 360; Wnum 262209 -> 1310785
  have s3 := horner_stage_frac 0xaf566247c05753b42892f77b67a6b7c6 o2 v 258 0x7a 240 262209
    (0xad4506af99be27419341e1816ff351 * 2^258 +
      (0xc926ddbecdeeb42e68cd16db7da8c1 * 2^126 + 0xdc07aff8276bde9a361278df6a10 * v) * v) hv
    (by norm_num) (by norm_num)
    (by have : (2:Nat)^121 < 2^256 := by norm_num
        omega)
    (by calc o2 * v < 2^121 * 2^120 := Nat.mul_lt_mul'' ho2lt hv
          _ < 2^256 := by norm_num)
    (by norm_num) (by norm_num) s2.1 s2.2
  rw [show (258:Nat)+0x7a-(240+120) = 20 from by norm_num,
    show (262209:Nat)+2^20 = 1310785 from by norm_num,
    show (240:Nat)+120 = 360 from by norm_num, show (258:Nat)+0x7a = 380 from by norm_num] at s3
  set o3 := evmAdd 0xaf566247c05753b42892f77b67a6b7c6 (evmShr 0x7a (evmMul o2 v)) with ho3
  have ho3lt : o3 < 2^129 := by
    have := (stage_bounds (c := 0xaf566247c05753b42892f77b67a6b7c6) (prev := o2) (v := v)
      (P := 2^121) (V := 2^120) (sh := 0x7a) ho2lt hv (by norm_num) (by norm_num)
      (by rw [pvd 121 120 122 119 (by norm_num)]; norm_num)).2
    rw [pvd 121 120 122 119 (by norm_num)] at this; omega
  -- stage 4: cum 380 -> 510, sh=130; p 360 -> 480; Wnum 1310785 -> 1075052609
  have s4 := horner_stage_frac 0x270a522f2b285a8374bfa62ed11c30f1 o3 v 380 0x82 360 1310785
    (0xaf566247c05753b42892f77b67a6b7c6 * 2^380 +
      (0xad4506af99be27419341e1816ff351 * 2^258 +
        (0xc926ddbecdeeb42e68cd16db7da8c1 * 2^126 + 0xdc07aff8276bde9a361278df6a10 * v) * v) * v) hv
    (by norm_num) (by norm_num)
    (by have : (2:Nat)^129 < 2^256 := by norm_num
        omega)
    (by calc o3 * v < 2^129 * 2^120 := Nat.mul_lt_mul'' ho3lt hv
          _ < 2^256 := by norm_num)
    (by norm_num) (by norm_num) s3.1 s3.2
  rw [show (380:Nat)+0x82-(360+120) = 30 from by norm_num,
    show (1310785:Nat)+2^30 = 1075052609 from by norm_num,
    show (360:Nat)+120 = 480 from by norm_num, show (380:Nat)+0x82 = 510 from by norm_num] at s4
  rw [hod]
  show 2^510 * evmAdd 0x270a522f2b285a8374bfa62ed11c30f1 (evmShr 0x82 (evmMul o3 v)) ≤ odNumV v ∧
    odNumV v < 2^510 * evmAdd 0x270a522f2b285a8374bfa62ed11c30f1 (evmShr 0x82 (evmMul o3 v)) +
      1075052609 * 2^480
  unfold odNumV
  constructor
  · have := s4.1; convert this using 2 <;> ring
  · have := s4.2; convert this using 2 <;> ring

/-- info: 'ExpYul.odTree_bracket' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms odTree_bracket

/-! ## The below-clamp target bound -/

open ExpRealSpec
open Common.Exp Common.RealExpBridge
open Real

noncomputable section

/-- Absolute value of the signed clamp boundary. -/
private abbrev CmaskAbs : Nat := 41446531673892822312323846185

/-- A lower cap certifying `10¹⁸ < exp(|Cmask| / 10²⁷)`. -/
private theorem exp_CmaskAbs_capLB : capLB CmaskAbs (10 ^ 27) (10 ^ 28 + 1) (10 ^ 10) := by
  refine ⟨129, ?_⟩
  unfold CmaskAbs
  decide +kernel

/-- An upper cap certifying `exp((|Cmask| - 1) / 10²⁷) < 10¹⁸`. -/
private theorem exp_CmaskAbs_pred_capUB : capUB (CmaskAbs - 1) (10 ^ 27) (10 ^ 28 - 1) (10 ^ 10) := by
  refine capUB_of_partial (by norm_num) (K := 129) ?_ ?_
  · unfold CmaskAbs
    norm_num
  · unfold CmaskAbs
    decide +kernel

private theorem exp_CmaskAbs_gt_WAD :
    (WAD : Real) < Real.exp ((CmaskAbs : Real) / (RAY : Real)) := by
  have hcap := le_exp_of_capLB (p := CmaskAbs) (q := 10 ^ 27)
    (y := 10 ^ 28 + 1) (w := 10 ^ 10) (by norm_num) (by norm_num) exp_CmaskAbs_capLB
  have htarget : (WAD : Real) < ((10 ^ 28 + 1 : Nat) : Real) / ((10 ^ 10 : Nat) : Real) := by
    unfold WAD
    norm_num
  have h := lt_of_lt_of_le htarget hcap
  simpa [RAY] using h

private theorem exp_CmaskAbs_pred_lt_WAD :
    Real.exp (((CmaskAbs - 1 : Nat) : Real) / (RAY : Real)) < (WAD : Real) := by
  have hcap := exp_le_of_capUB (p := CmaskAbs - 1) (q := 10 ^ 27)
    (y := 10 ^ 28 - 1) (w := 10 ^ 10) (by norm_num) (by norm_num) exp_CmaskAbs_pred_capUB
  have htarget : ((10 ^ 28 - 1 : Nat) : Real) / ((10 ^ 10 : Nat) : Real) < (WAD : Real) := by
    unfold WAD
    norm_num
  have h := lt_of_le_of_lt hcap htarget
  simpa [RAY] using h

/-- At `Cmask`, the real target is below one output unit. -/
theorem expRayToWadTarget_Cmask_lt_one : expRayToWadTarget (int256 Cmask) < 1 := by
  have hCm : int256 Cmask = - (CmaskAbs : Int) := by
    rw [int256_Cmask]
    norm_num [CmaskAbs]
  have hgt := exp_CmaskAbs_gt_WAD
  unfold expRayToWadTarget
  rw [hCm]
  simp only [Int.cast_neg, Int.cast_natCast]
  rw [neg_div, Real.exp_neg, ← div_eq_mul_inv]
  rw [div_lt_iff₀ (Real.exp_pos ((CmaskAbs : Real) / (RAY : Real)))]
  simpa using hgt

/-- Just above `Cmask`, the real target is above one output unit. -/
theorem one_lt_expRayToWadTarget_Cmask_succ : 1 < expRayToWadTarget (int256 Cmask + 1) := by
  have hCm : int256 Cmask = - (CmaskAbs : Int) := by
    rw [int256_Cmask]
    norm_num [CmaskAbs]
  have hpred : int256 Cmask + 1 = - ((CmaskAbs - 1 : Nat) : Int) := by
    rw [hCm]
    norm_num [CmaskAbs]
  have hlt := exp_CmaskAbs_pred_lt_WAD
  unfold expRayToWadTarget
  rw [hpred]
  simp only [Int.cast_neg, Int.cast_natCast]
  rw [neg_div, Real.exp_neg, ← div_eq_mul_inv]
  rw [lt_div_iff₀ (Real.exp_pos (((CmaskAbs - 1 : Nat) : Real) / (RAY : Real)))]
  simpa using hlt

/-- The real target is monotone in the signed input. -/
theorem expRayToWadTarget_mono {a b : Int} (h : a ≤ b) :
    expRayToWadTarget a ≤ expRayToWadTarget b := by
  unfold expRayToWadTarget
  have hRAY : (0 : Real) < (RAY : Real) := by
    unfold RAY
    norm_num
  have hargs : (a : Real) / (RAY : Real) ≤ (b : Real) / (RAY : Real) := by
    rw [div_le_div_iff_of_pos_right hRAY]
    exact_mod_cast h
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hargs) (by unfold WAD; norm_num)

/-- `Cmask` is the exact signed boundary where the real target crosses one output unit. -/
theorem expRayToWadTarget_lt_one_iff (z : Int) :
    expRayToWadTarget z < 1 ↔ z ≤ int256 Cmask := by
  constructor
  · intro hz
    by_contra hnot
    push_neg at hnot
    have hsucc : int256 Cmask + 1 ≤ z := by omega
    have hmono := expRayToWadTarget_mono hsucc
    have h1 := one_lt_expRayToWadTarget_Cmask_succ
    linarith
  · intro hz
    have hmono := expRayToWadTarget_mono hz
    have hlt := expRayToWadTarget_Cmask_lt_one
    linarith

/-- Below the clamp boundary the target is under one output unit. -/
theorem belowC_target_lt_one {x : Nat} (hxle : int256 x ≤ int256 Cmask) :
    expRayToWadTarget (int256 x) < 1 :=
  (expRayToWadTarget_lt_one_iff (int256 x)).2 hxle

/-- info: 'ExpYul.belowC_target_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms belowC_target_lt_one

end

end ExpYul

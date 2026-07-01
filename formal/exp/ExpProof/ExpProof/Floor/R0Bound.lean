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
`E = 10¹⁸·exp(int256 x / 10²⁷)` across the octave shift `2^(126 − k)`. This file builds two
ingredients of that discharge:

* the **Horner-truncation bridge** for the even accumulator — the runtime `evTree x`, which
  truncates each Horner `>>` stage, brackets the exact even polynomial `evNumV (vTree x)` (a degree-5
  polynomial in `v` at the cleared scale `2^553`) within `2` units: per-stage floor losses telescope
  with shrinking amplification (each stage shift exceeds `126 = ⌈log₂ v⌉`);
* the self-contained **below-clamp bound** — below the clamp boundary the target is under one output
  unit — directly from a `Real.exp` rational bound.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-! ## Gap-2: the even Horner accumulator brackets the exact polynomial

Each runtime Horner stage `evmAdd c (evmShr sh (evmMul prev v))` is the integer floor
`c + ⌊prev·v / 2^sh⌋`; the floor loss `< 1` at scale `2^sh`. Cleared to the common scale `2^553`
the runtime accumulator `evTree x` brackets the exact degree-5 polynomial `evNumV (vTree x)` within
`2·2^553`: the propagated loss stays below `2^sh` because every stage shift exceeds the `126`-bit
width of `v = vTree x`. -/

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

theorem tele_step (e0 e1 v A c0 s E0 : Nat)
    (hv : v < 2^126) (hs : 127 ≤ s) (hAe1 : A ≤ e1)
    (hb0lo : 2^c0 * e0 ≤ E0) (hb0hi : E0 < 2^c0 * e0 + 2 * 2^c0)
    (hslo : 2^s * (e1 - A) ≤ e0 * v) (hshi : e0 * v < 2^s * (e1 - A) + 2^s) :
    2^(c0+s) * e1 ≤ A * 2^(c0+s) + E0 * v ∧
      A * 2^(c0+s) + E0 * v < 2^(c0+s) * e1 + 2 * 2^(c0+s) := by
  have hpc0 : (0:Nat) < 2^c0 := Nat.two_pow_pos _
  have hps : (0:Nat) < 2^s := Nat.two_pow_pos _
  have hsplit : (2:Nat)^(c0+s) = 2^c0 * 2^s := by rw [Nat.pow_add]
  set d := e1 - A with hd
  have he1eq : e1 = A + d := by omega
  have hvs : 2 * 2^c0 * v < 2^(c0+s) := by
    rw [hsplit]
    have h2v : 2 * v < 2^s := by
      have h127 : (2:Nat)*2^126 = 2^127 := by ring
      have h128 : (2:Nat)^127 ≤ 2^s := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    calc 2*2^c0*v = 2^c0*(2*v) := by ring
      _ < 2^c0 * 2^s := (Nat.mul_lt_mul_left hpc0).mpr h2v
  rw [hsplit, he1eq]
  have key_lo : 2^c0 * 2^s * d ≤ E0 * v := by
    calc 2^c0 * 2^s * d = 2^c0 * (2^s * d) := by ring
      _ ≤ 2^c0 * (e0 * v) := by gcongr
      _ = (2^c0 * e0) * v := by ring
      _ ≤ E0 * v := by gcongr
  have hps2 : (0:Nat) < 2^(c0+s) := Nat.two_pow_pos _
  have key_hi : E0 * v < 2^c0 * 2^s * d + 2 * 2^(c0+s) := by
    rcases Nat.eq_zero_or_pos v with hv0 | hv0
    · subst hv0; simpa using hps2
    have h1 : E0 * v < (2^c0 * e0 + 2*2^c0) * v := (Nat.mul_lt_mul_right hv0).mpr hb0hi
    have h2 : (2^c0 * e0 + 2*2^c0) * v = 2^c0 * (e0*v) + 2*2^c0*v := by ring
    have h3 : 2^c0 * (e0*v) < 2^c0 * (2^s*d + 2^s) := (Nat.mul_lt_mul_left hpc0).mpr hshi
    have h4 : 2^c0 * (2^s*d+2^s) = 2^c0*2^s*d + 2^c0*2^s := by ring
    rw [hsplit] at hvs
    omega
  constructor
  · nlinarith [key_lo]
  · nlinarith [key_hi]

/-! ## The fractional telescoping bound

The integer `tele_step` above yields a per-stage `+2` width because it carries the input width
verbatim (`E0 < 2^c0·e0 + 2·2^c0`). The *fractional* version tracks the exact deficit width as
`Wnum·2^p` (a dyadic rational `Wnum/2^(cum-p)` at the cumulative scale `2^cum`). Across a stage with
shift `s ≥ 127` the carried width is attenuated by `v/2^s ≤ 2^(126-s) < 1`, so the width evolves as
`W' = W·2^(126-s) + 1`. With `r_i = 2^(126-s_i) < 1` the widths stay strictly below `1/(1−max r)`,
recovering the true ≈1.02-unit gap-2 envelope instead of the loose `+2`.

The state is `2^cum·e ≤ E < 2^cum·e + Wnum·2^p` with `p ≤ cum` (the width exponent). One stage with
shift `s` (constant `A`, `e1 = A + ⌊e0·v/2^s⌋`) produces the new width `Wnum' = Wnum + 2^(cum+s−p−126)`
at exponent `p' = p + 126` and scale `cum' = cum + s`. -/
theorem tele_step_frac (e0 e1 v A cum s p Wnum E0 : Nat)
    (hv : v < 2^126) (hs : 126 ≤ s) (hAe1 : A ≤ e1) (hpcum : p + 126 ≤ cum + s)
    (hb0lo : 2^cum * e0 ≤ E0) (hb0hi : E0 < 2^cum * e0 + Wnum * 2^p)
    (hslo : 2^s * (e1 - A) ≤ e0 * v) (hshi : e0 * v < 2^s * (e1 - A) + 2^s) :
    2^(cum+s) * e1 ≤ A * 2^(cum+s) + E0 * v ∧
      A * 2^(cum+s) + E0 * v <
        2^(cum+s) * e1 + (Wnum + 2^(cum+s-(p+126))) * 2^(p+126) := by
  -- factor the relevant power identities, then abstract every `2^…` to an opaque var
  have hsplit : (2:Nat)^(cum+s) = 2^cum * 2^s := by rw [Nat.pow_add]
  -- key: 2^cum · 2^s = 2^(p+126) · 2^(cum+s-(p+126)) = 2^p · 2^126 · G
  have hG : (2:Nat)^cum * 2^s = (2^p * 2^126) * 2^(cum+s-(p+126)) := by
    rw [show (2:Nat)^p * 2^126 = 2^(p+126) from by rw [Nat.pow_add],
      ← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
  have hPP126 : (2:Nat)^(p+126) = 2^p * 2^126 := by rw [Nat.pow_add]
  have hP126 : (0:Nat) < 2^126 := Nat.two_pow_pos _
  have hPcum : (0:Nat) < 2^cum := Nat.two_pow_pos _
  set d := e1 - A with hd
  have he1eq : e1 = A + d := by omega
  -- abstract powers
  set P := (2:Nat)^cum with hPdef
  set Q := (2:Nat)^s with hQdef
  set R := (2:Nat)^p with hRdef
  set H := (2:Nat)^126 with hHdef
  set G := (2:Nat)^(cum+s-(p+126)) with hGdef
  -- collected facts in abstract form
  rw [hsplit, he1eq]
  rw [show (2:Nat)^(p+126) = R * H from hPP126]
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

theorem ev0_exact {v : Nat} (hv : v < 2 ^ 126) :
    2^0x1d * (evmAdd 0xb9aacfad41060587203a79af0ebc (evmShr 0x1d v) - 0xb9aacfad41060587203a79af0ebc) ≤ v ∧
      v < 2^0x1d * (evmAdd 0xb9aacfad41060587203a79af0ebc (evmShr 0x1d v) - 0xb9aacfad41060587203a79af0ebc) + 2^0x1d := by
  have hshr : evmShr 0x1d v = v / 2^0x1d := evmShr_eq_div (by norm_num) (by omega)
  have ht : v / 2^0x1d < 2^97 := by
    have : v / 2^0x1d < 2^126/2^0x1d := Nat.div_lt_div_of_lt_of_dvd (by norm_num) hv
    have he : (2:Nat)^126/2^0x1d = 2^97 := by rw [Nat.pow_div (by norm_num) (by norm_num)]
    omega
  rw [hshr, evmAdd_eq_nat (by norm_num) (by omega) (by omega), Nat.add_sub_cancel_left]
  have hpos : 0 < 2^0x1d := Nat.two_pow_pos _
  have hdm := Nat.div_add_mod v (2^0x1d)
  have hmod := Nat.mod_lt v hpos
  generalize v / 2^0x1d = q at *
  generalize v % 2^0x1d = r at *
  omega

def evNumV (v : Nat) : Nat :=
  let e0 := 0xb9aacfad41060587203a79af0ebc * 2^29 + v
  let e1 := 0x9a036222e11aee18465042f8ea64c8 * 2^159 + e0 * v
  let e2 := 0x9064d965e1c4863b73604e0ddbec53f9 * 2^287 + e1 * v
  let e3 := 0x93f11e65781741b92fa7fc4f4fffcca2 * 2^421 + e2 * v
  0x4e14a45e8ec305e233e11b4174e214ac * 2^553 + e3 * v

/-- One telescoped runtime Horner stage: the stage value `evmAdd c (shr sh (mul prev v))` cleared to
scale `2^(cum+sh)` brackets `c·2^(cum+sh) + Eprev·v` within `2·2^(cum+sh)`, given the cumulative
bracket on `prev` at scale `2^cum`. -/
theorem horner_stage (c P prev v cum sh Eprev : Nat)
    (hv : v < 2^126) (hs : 127 ≤ sh) (hsh256 : sh < 256) (hprevlt : prev < P) (hPV : P * 2^126 < 2^256)
    (hsum : c + P * 2^126 / 2^sh < 2^256) (hclt : c < 2^256)
    (hElo : 2^cum * prev ≤ Eprev) (hEhi : Eprev < 2^cum * prev + 2 * 2^cum) :
    2^(cum+sh) * (evmAdd c (evmShr sh (evmMul prev v))) ≤ c * 2^(cum+sh) + Eprev * v ∧
      c * 2^(cum+sh) + Eprev * v < 2^(cum+sh) * (evmAdd c (evmShr sh (evmMul prev v))) + 2 * 2^(cum+sh) := by
  have hprev256 : prev < 2^256 := by have : P ≤ 2^256 := by omega
                                     omega
  have hv256 : v < 2^256 := by have : (2:Nat)^126 < 2^256 := by norm_num
                               omega
  have hpv : prev * v < 2^256 := lt_of_lt_of_le (Nat.mul_lt_mul'' hprevlt hv) (by omega)
  have hsum' : c + prev * v / 2^sh < 2^256 := by
    have : prev * v / 2^sh ≤ P * 2^126 / 2^sh := by
      apply Nat.div_le_div_right; exact Nat.le_of_lt (Nat.mul_lt_mul'' hprevlt hv)
    omega
  have hst := stage_exact hprev256 hv256 hpv hsh256 hclt hsum'
  set ev1 := evmAdd c (evmShr sh (evmMul prev v)) with hev1
  have hge : c ≤ ev1 := by
    rw [hev1, evmAdd_eq_nat hclt (by exact evmShr_lt _ _) (by
      have hmul : evmMul prev v = prev * v := evmMul_eq_nat hprev256 hv256 hpv
      have : evmShr sh (evmMul prev v) = prev*v/2^sh := by rw [hmul]; exact evmShr_eq_div (by omega) hpv
      rw [this]; omega)]
    omega
  exact tele_step prev ev1 v c cum sh Eprev hv hs hge hElo hEhi hst.1 hst.2

/-- The fractional version of `horner_stage`: a runtime Horner stage propagates a *dyadic-fraction*
deficit width `Wnum·2^p` into `(Wnum + 2^(cum+sh−p−126))·2^(p+126)` (the carried width is attenuated
by `v/2^sh ≤ 2^(126−sh) < 1`). Consumes `tele_step_frac`. -/
theorem horner_stage_frac (c P prev v cum sh p Wnum Eprev : Nat)
    (hv : v < 2^126) (hs : 126 ≤ sh) (hsh256 : sh < 256) (hprevlt : prev < P)
    (hPV : P * 2^126 < 2^256) (hpcum : p + 126 ≤ cum + sh)
    (hsum : c + P * 2^126 / 2^sh < 2^256) (hclt : c < 2^256)
    (hElo : 2^cum * prev ≤ Eprev) (hEhi : Eprev < 2^cum * prev + Wnum * 2^p) :
    2^(cum+sh) * (evmAdd c (evmShr sh (evmMul prev v))) ≤ c * 2^(cum+sh) + Eprev * v ∧
      c * 2^(cum+sh) + Eprev * v <
        2^(cum+sh) * (evmAdd c (evmShr sh (evmMul prev v))) +
          (Wnum + 2^(cum+sh-(p+126))) * 2^(p+126) := by
  have hprev256 : prev < 2^256 := by have : P ≤ 2^256 := by omega
                                     omega
  have hv256 : v < 2^256 := by have : (2:Nat)^126 < 2^256 := by norm_num
                               omega
  have hpv : prev * v < 2^256 := lt_of_lt_of_le (Nat.mul_lt_mul'' hprevlt hv) (by omega)
  have hsum' : c + prev * v / 2^sh < 2^256 := by
    have : prev * v / 2^sh ≤ P * 2^126 / 2^sh := by
      apply Nat.div_le_div_right; exact Nat.le_of_lt (Nat.mul_lt_mul'' hprevlt hv)
    omega
  have hst := stage_exact hprev256 hv256 hpv hsh256 hclt hsum'
  set ev1 := evmAdd c (evmShr sh (evmMul prev v)) with hev1
  have hge : c ≤ ev1 := by
    rw [hev1, evmAdd_eq_nat hclt (by exact evmShr_lt _ _) (by
      have hmul : evmMul prev v = prev * v := evmMul_eq_nat hprev256 hv256 hpv
      have : evmShr sh (evmMul prev v) = prev*v/2^sh := by rw [hmul]; exact evmShr_eq_div (by omega) hpv
      rw [this]; omega)]
    omega
  exact tele_step_frac prev ev1 v c cum sh p Wnum Eprev hv hs hge hpcum hElo hEhi hst.1 hst.2


theorem evTree_bracket {x : Nat} (hv : vTree x < 2 ^ 126) :
    2^553 * evTree x ≤ evNumV (vTree x) ∧ evNumV (vTree x) < 2^553 * evTree x + 1065041 * 2^533 := by
  have hev : evTree x =
      evmAdd 0x4e14a45e8ec305e233e11b4174e214ac (evmShr 0x84 (evmMul
      (evmAdd 0x93f11e65781741b92fa7fc4f4fffcca2 (evmShr 0x86 (evmMul
      (evmAdd 0x9064d965e1c4863b73604e0ddbec53f9 (evmShr 0x80 (evmMul
      (evmAdd 0x9a036222e11aee18465042f8ea64c8 (evmShr 0x82 (evmMul
      (evmAdd 0xb9aacfad41060587203a79af0ebc (evmShr 0x1d (vTree x))) (vTree x)))) (vTree x)))) (vTree x)))) (vTree x))) := rfl
  set v := vTree x with hvdef
  -- stage 0: width 1·2^29 (p=29, Wnum=1)
  have h0 := ev0_exact hv
  set e0 := evmAdd 0xb9aacfad41060587203a79af0ebc (evmShr 0x1d v) with he0
  have he0lt : e0 < 2 ^ 113 := ev0_lt hv
  have he0ge : 0xb9aacfad41060587203a79af0ebc ≤ e0 := ev0_ge hv
  have h29 : (0x1d : Nat) = 29 := by norm_num
  rw [h29] at h0
  have hE0lo : 2^29 * e0 ≤ 0xb9aacfad41060587203a79af0ebc * 2^29 + v := by have := h0.1; omega
  have hE0hi : 0xb9aacfad41060587203a79af0ebc * 2^29 + v < 2^29 * e0 + 1 * 2^29 := by have := h0.2; omega
  -- stage 1: cum 29 -> 159, sh=130; p 29 -> 155; Wnum 1 -> 17
  have s1 := horner_stage_frac 0x9a036222e11aee18465042f8ea64c8 (2^113) e0 v 29 0x82 29 1
    (0xb9aacfad41060587203a79af0ebc * 2^29 + v) hv (by norm_num) (by norm_num) he0lt (by norm_num)
    (by norm_num) (by rw [pvd 113 126 130 109 (by norm_num)]; norm_num) (by norm_num) hE0lo hE0hi
  -- normalise the stage-1 width `(1 + 2^(159-155))·2^155` to `17·2^155`
  rw [show (29:Nat)+0x82-(29+126) = 4 from by norm_num, show (1:Nat)+2^4 = 17 from by norm_num,
    show (29:Nat)+126 = 155 from by norm_num, show (29:Nat)+0x82 = 159 from by norm_num] at s1
  set e1 := evmAdd 0x9a036222e11aee18465042f8ea64c8 (evmShr 0x82 (evmMul e0 v)) with he1
  have he1lt : e1 < 2^121 := by
    have := (stage_bounds (c := 0x9a036222e11aee18465042f8ea64c8) (prev := e0) (v := v)
      (P := 2^113) (V := 2^126) (sh := 0x82) he0lt hv (by norm_num) (by norm_num)
      (by rw [pvd 113 126 130 109 (by norm_num)]; norm_num)).2
    rw [pvd 113 126 130 109 (by norm_num)] at this; omega
  -- stage 2: cum 159 -> 287, sh=128; p 155 -> 281; Wnum 17 -> 81
  have s2 := horner_stage_frac 0x9064d965e1c4863b73604e0ddbec53f9 (2^121) e1 v 159 0x80 155 17
    (0x9a036222e11aee18465042f8ea64c8 * 2^159 + (0xb9aacfad41060587203a79af0ebc * 2^29 + v) * v)
    hv (by norm_num) (by norm_num) he1lt (by norm_num)
    (by norm_num) (by rw [pvd 121 126 128 119 (by norm_num)]; norm_num) (by norm_num) s1.1 s1.2
  rw [show (159:Nat)+0x80-(155+126) = 6 from by norm_num, show (17:Nat)+2^6 = 81 from by norm_num,
    show (155:Nat)+126 = 281 from by norm_num, show (159:Nat)+0x80 = 287 from by norm_num] at s2
  set e2 := evmAdd 0x9064d965e1c4863b73604e0ddbec53f9 (evmShr 0x80 (evmMul e1 v)) with he2
  have he2lt : e2 < 2^129 := by
    have := (stage_bounds (c := 0x9064d965e1c4863b73604e0ddbec53f9) (prev := e1) (v := v)
      (P := 2^121) (V := 2^126) (sh := 0x80) he1lt hv (by norm_num) (by norm_num)
      (by rw [pvd 121 126 128 119 (by norm_num)]; norm_num)).2
    rw [pvd 121 126 128 119 (by norm_num)] at this; omega
  -- stage 3: cum 287 -> 421, sh=134; p 281 -> 407; Wnum 81 -> 16465
  have s3 := horner_stage_frac 0x93f11e65781741b92fa7fc4f4fffcca2 (2^129) e2 v 287 0x86 281 81
    (0x9064d965e1c4863b73604e0ddbec53f9 * 2^287 +
      (0x9a036222e11aee18465042f8ea64c8 * 2^159 + (0xb9aacfad41060587203a79af0ebc * 2^29 + v) * v) * v)
    hv (by norm_num) (by norm_num) he2lt (by norm_num)
    (by norm_num) (by rw [pvd 129 126 134 121 (by norm_num)]; norm_num) (by norm_num) s2.1 s2.2
  rw [show (287:Nat)+0x86-(281+126) = 14 from by norm_num, show (81:Nat)+2^14 = 16465 from by norm_num,
    show (281:Nat)+126 = 407 from by norm_num, show (287:Nat)+0x86 = 421 from by norm_num] at s3
  set e3 := evmAdd 0x93f11e65781741b92fa7fc4f4fffcca2 (evmShr 0x86 (evmMul e2 v)) with he3
  have he3lt : e3 < 2^129 := by
    have := (stage_bounds (c := 0x93f11e65781741b92fa7fc4f4fffcca2) (prev := e2) (v := v)
      (P := 2^129) (V := 2^126) (sh := 0x86) he2lt hv (by norm_num) (by norm_num)
      (by rw [pvd 129 126 134 121 (by norm_num)]; norm_num)).2
    rw [pvd 129 126 134 121 (by norm_num)] at this; omega
  -- stage 4: cum 421 -> 553, sh=132; p 407 -> 533; Wnum 16465 -> 1065041
  have s4 := horner_stage_frac 0x4e14a45e8ec305e233e11b4174e214ac (2^129) e3 v 421 0x84 407 16465
    (0x93f11e65781741b92fa7fc4f4fffcca2 * 2^421 +
      (0x9064d965e1c4863b73604e0ddbec53f9 * 2^287 +
        (0x9a036222e11aee18465042f8ea64c8 * 2^159 +
          (0xb9aacfad41060587203a79af0ebc * 2^29 + v) * v) * v) * v)
    hv (by norm_num) (by norm_num) he3lt (by norm_num)
    (by norm_num) (by rw [pvd 129 126 132 123 (by norm_num)]; norm_num) (by norm_num) s3.1 s3.2
  rw [show (421:Nat)+0x84-(407+126) = 20 from by norm_num,
    show (16465:Nat)+2^20 = 1065041 from by norm_num,
    show (407:Nat)+126 = 533 from by norm_num, show (421:Nat)+0x84 = 553 from by norm_num] at s4
  -- assemble: evTree x = e4 (the stage-4 value), evNumV v = the cumulative E4.
  rw [hev]
  show 2^553 * evmAdd 0x4e14a45e8ec305e233e11b4174e214ac (evmShr 0x84 (evmMul e3 v)) ≤ evNumV v ∧
    evNumV v < 2^553 * evmAdd 0x4e14a45e8ec305e233e11b4174e214ac (evmShr 0x84 (evmMul e3 v)) + 1065041 * 2^533
  unfold evNumV
  constructor
  · have := s4.1
    convert this using 2 <;> ring
  · have := s4.2
    convert this using 2 <;> ring


/-- info: 'ExpYul.evTree_bracket' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evTree_bracket

/-! ## Gap-2: the odd Horner accumulator brackets the exact polynomial

The odd accumulator starts at the leading constant `B4` (scale `0`) and runs four mul/shr stages
(shifts `0x83, 0x89, 0x7f, 0x87`, cumulative `131, 268, 395, 530`). Cleared to scale `2^530` the
runtime `odTree x` brackets the exact degree-4 polynomial `odNumV (vTree x)` within `2·2^530`. -/

/-- Exact integer odd-Horner numerator (degree-4 in `v`, scale `2^530`). -/
def odNumV (v : Nat) : Nat :=
  let o1 := 0xc926ddbf3830ca5561cc01585402d0 * 2^131 + 0xdc07aff85e5bb5629d0fb64a84bb * v
  let o2 := 0xad4506b00b1246c7e5b4fd33e1201b * 2^268 + o1 * v
  let o3 := 0xaf5662483c4ce783a9ef5fe025f42e9e * 2^395 + o2 * v
  0x270a522f476182f119f08da0ba710a56 * 2^530 + o3 * v

/-- Runtime odd-Horner accumulator brackets the exact polynomial within `1.003·2^530` (the
fractional gap-2 envelope) at scale `2^530`. -/
theorem odTree_bracket {x : Nat} (hv : vTree x < 2 ^ 126) :
    2^530 * odTree x ≤ odNumV (vTree x) ∧ odNumV (vTree x) < 2^530 * odTree x + 67305505 * 2^504 := by
  have hod : odTree x =
      evmAdd 0x270a522f476182f119f08da0ba710a56 (evmShr 0x87 (evmMul
      (evmAdd 0xaf5662483c4ce783a9ef5fe025f42e9e (evmShr 0x7f (evmMul
      (evmAdd 0xad4506b00b1246c7e5b4fd33e1201b (evmShr 0x89 (evmMul
      (evmAdd 0xc926ddbf3830ca5561cc01585402d0 (evmShr 0x83 (evmMul
      0xdc07aff85e5bb5629d0fb64a84bb (vTree x)))) (vTree x)))) (vTree x)))) (vTree x))) := rfl
  set v := vTree x with hvdef
  -- the leading constant is exact; track it as width 1·2^0 (B0 < B0 + 1)
  have hB4lo : 2^0 * 0xdc07aff85e5bb5629d0fb64a84bb ≤ 0xdc07aff85e5bb5629d0fb64a84bb := by norm_num
  have hB4hi : (0xdc07aff85e5bb5629d0fb64a84bb : Nat) < 2^0 * 0xdc07aff85e5bb5629d0fb64a84bb + 1 * 2^0 := by norm_num
  -- stage 1: cum 0 -> 131, sh=131; p 0 -> 126; Wnum 1 -> 33
  have s1 := horner_stage_frac 0xc926ddbf3830ca5561cc01585402d0 (2^112) 0xdc07aff85e5bb5629d0fb64a84bb v 0 0x83 0 1
    0xdc07aff85e5bb5629d0fb64a84bb hv (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by rw [pvd 112 126 131 107 (by norm_num)]; norm_num) (by norm_num) hB4lo hB4hi
  rw [show (0:Nat)+0x83-(0+126) = 5 from by norm_num, show (1:Nat)+2^5 = 33 from by norm_num,
    show (0:Nat)+126 = 126 from by norm_num, show (0:Nat)+0x83 = 131 from by norm_num] at s1
  set o1 := evmAdd 0xc926ddbf3830ca5561cc01585402d0 (evmShr 0x83 (evmMul 0xdc07aff85e5bb5629d0fb64a84bb v)) with ho1
  have ho1lt : o1 < 2^121 := by
    have := (stage_bounds (c := 0xc926ddbf3830ca5561cc01585402d0) (prev := 0xdc07aff85e5bb5629d0fb64a84bb) (v := v)
      (P := 2^112) (V := 2^126) (sh := 0x83) (by norm_num) hv (by norm_num) (by norm_num)
      (by rw [pvd 112 126 131 107 (by norm_num)]; norm_num)).2
    rw [pvd 112 126 131 107 (by norm_num)] at this; omega
  -- stage 2: cum 131 -> 268, sh=137; p 126 -> 252; Wnum 33 -> 65569
  have s2 := horner_stage_frac 0xad4506b00b1246c7e5b4fd33e1201b (2^121) o1 v 131 0x89 126 33
    (0xc926ddbf3830ca5561cc01585402d0 * 2^131 + 0xdc07aff85e5bb5629d0fb64a84bb * v) hv (by norm_num) (by norm_num) ho1lt (by norm_num)
    (by norm_num) (by rw [pvd 121 126 137 110 (by norm_num)]; norm_num) (by norm_num) s1.1 s1.2
  rw [show (131:Nat)+0x89-(126+126) = 16 from by norm_num, show (33:Nat)+2^16 = 65569 from by norm_num,
    show (126:Nat)+126 = 252 from by norm_num, show (131:Nat)+0x89 = 268 from by norm_num] at s2
  set o2 := evmAdd 0xad4506b00b1246c7e5b4fd33e1201b (evmShr 0x89 (evmMul o1 v)) with ho2
  have ho2lt : o2 < 2^121 := by
    have := (stage_bounds (c := 0xad4506b00b1246c7e5b4fd33e1201b) (prev := o1) (v := v)
      (P := 2^121) (V := 2^126) (sh := 0x89) ho1lt hv (by norm_num) (by norm_num)
      (by rw [pvd 121 126 137 110 (by norm_num)]; norm_num)).2
    rw [pvd 121 126 137 110 (by norm_num)] at this; omega
  -- stage 3: cum 268 -> 395, sh=127; p 252 -> 378; Wnum 65569 -> 196641
  have s3 := horner_stage_frac 0xaf5662483c4ce783a9ef5fe025f42e9e (2^121) o2 v 268 0x7f 252 65569
    (0xad4506b00b1246c7e5b4fd33e1201b * 2^268 +
      (0xc926ddbf3830ca5561cc01585402d0 * 2^131 + 0xdc07aff85e5bb5629d0fb64a84bb * v) * v) hv (by norm_num) (by norm_num) ho2lt (by norm_num)
    (by norm_num) (by rw [pvd 121 126 127 120 (by norm_num)]; norm_num) (by norm_num) s2.1 s2.2
  rw [show (268:Nat)+0x7f-(252+126) = 17 from by norm_num, show (65569:Nat)+2^17 = 196641 from by norm_num,
    show (252:Nat)+126 = 378 from by norm_num, show (268:Nat)+0x7f = 395 from by norm_num] at s3
  set o3 := evmAdd 0xaf5662483c4ce783a9ef5fe025f42e9e (evmShr 0x7f (evmMul o2 v)) with ho3
  have ho3lt : o3 < 2^129 := by
    have := (stage_bounds (c := 0xaf5662483c4ce783a9ef5fe025f42e9e) (prev := o2) (v := v)
      (P := 2^121) (V := 2^126) (sh := 0x7f) ho2lt hv (by norm_num) (by norm_num)
      (by rw [pvd 121 126 127 120 (by norm_num)]; norm_num)).2
    rw [pvd 121 126 127 120 (by norm_num)] at this; omega
  -- stage 4: cum 395 -> 530, sh=135; p 378 -> 504; Wnum 196641 -> 67305505
  have s4 := horner_stage_frac 0x270a522f476182f119f08da0ba710a56 (2^129) o3 v 395 0x87 378 196641
    (0xaf5662483c4ce783a9ef5fe025f42e9e * 2^395 +
      (0xad4506b00b1246c7e5b4fd33e1201b * 2^268 +
        (0xc926ddbf3830ca5561cc01585402d0 * 2^131 + 0xdc07aff85e5bb5629d0fb64a84bb * v) * v) * v) hv (by norm_num) (by norm_num) ho3lt (by norm_num)
    (by norm_num) (by rw [pvd 129 126 135 120 (by norm_num)]; norm_num) (by norm_num) s3.1 s3.2
  rw [show (395:Nat)+0x87-(378+126) = 26 from by norm_num,
    show (196641:Nat)+2^26 = 67305505 from by norm_num,
    show (378:Nat)+126 = 504 from by norm_num, show (395:Nat)+0x87 = 530 from by norm_num] at s4
  rw [hod]
  show 2^530 * evmAdd 0x270a522f476182f119f08da0ba710a56 (evmShr 0x87 (evmMul o3 v)) ≤ odNumV v ∧
    odNumV v < 2^530 * evmAdd 0x270a522f476182f119f08da0ba710a56 (evmShr 0x87 (evmMul o3 v)) + 67305505 * 2^504
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

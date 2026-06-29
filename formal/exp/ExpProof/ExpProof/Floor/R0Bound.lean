import ExpProof.Floor.Fold
import ExpProof.Floor.TBound
import ExpProof.Mono.Quot
import Mathlib.Data.Complex.ExponentialBounds

/-!
# Discharging the runtime `r0` bound

`RuntimeR0Bound` (the single analytic obligation for the public floor brackets) brackets the Q126 quotient
`r0Tree x` against the target `E = 10¹⁸·exp(int256 x / 10²⁷)` across the octave shift `2^(126 − k)`.
This file builds two ingredients of that discharge:

* the **gap-2 (Horner-truncation) bridge** for the even accumulator — the runtime `evTree x`, which
  truncates each Horner `>>` stage, brackets the exact even polynomial `evNumV (vTree x)` (a degree-5
  polynomial in `v` at the cleared scale `2^553`) within `2` units: per-stage floor losses telescope
  with shrinking amplification (each stage shift exceeds `126 = ⌈log₂ v⌉`);
* the self-contained **`belowC`** field — below the clamp boundary the target is under one output
  unit — directly from a `Real.exp` rational bound.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

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


theorem evTree_bracket {x : Nat} (hv : vTree x < 2 ^ 126) :
    2^553 * evTree x ≤ evNumV (vTree x) ∧ evNumV (vTree x) < 2^553 * evTree x + 2 * 2^553 := by
  have hev : evTree x =
      evmAdd 0x4e14a45e8ec305e233e11b4174e214ac (evmShr 0x84 (evmMul
      (evmAdd 0x93f11e65781741b92fa7fc4f4fffcca2 (evmShr 0x86 (evmMul
      (evmAdd 0x9064d965e1c4863b73604e0ddbec53f9 (evmShr 0x80 (evmMul
      (evmAdd 0x9a036222e11aee18465042f8ea64c8 (evmShr 0x82 (evmMul
      (evmAdd 0xb9aacfad41060587203a79af0ebc (evmShr 0x1d (vTree x))) (vTree x)))) (vTree x)))) (vTree x)))) (vTree x))) := rfl
  set v := vTree x with hvdef
  -- stage 0
  have h0 := ev0_exact hv
  set e0 := evmAdd 0xb9aacfad41060587203a79af0ebc (evmShr 0x1d v) with he0
  have he0lt : e0 < 2 ^ 113 := ev0_lt hv
  have he0ge : 0xb9aacfad41060587203a79af0ebc ≤ e0 := ev0_ge hv
  -- E0 = A4*2^29 + v; bracket 2^29*e0 <= E0 < 2^29*e0 + 2*2^29
  have h29 : (0x1d : Nat) = 29 := by norm_num
  rw [h29] at h0
  have hE0lo : 2^29 * e0 ≤ 0xb9aacfad41060587203a79af0ebc * 2^29 + v := by have := h0.1; omega
  have hE0hi : 0xb9aacfad41060587203a79af0ebc * 2^29 + v < 2^29 * e0 + 2 * 2^29 := by have := h0.2; omega
  -- stage 1: cum 29 -> 159, sh=0x82=130, P=2^113
  have s1 := horner_stage 0x9a036222e11aee18465042f8ea64c8 (2^113) e0 v 29 0x82
    (0xb9aacfad41060587203a79af0ebc * 2^29 + v) hv (by norm_num) (by norm_num) he0lt (by norm_num)
    (by rw [pvd 113 126 130 109 (by norm_num)]; norm_num) (by norm_num) hE0lo hE0hi
  set e1 := evmAdd 0x9a036222e11aee18465042f8ea64c8 (evmShr 0x82 (evmMul e0 v)) with he1
  have he1lt : e1 < 2^121 := by
    have := (stage_bounds (c := 0x9a036222e11aee18465042f8ea64c8) (prev := e0) (v := v)
      (P := 2^113) (V := 2^126) (sh := 0x82) he0lt hv (by norm_num) (by norm_num)
      (by rw [pvd 113 126 130 109 (by norm_num)]; norm_num)).2
    rw [pvd 113 126 130 109 (by norm_num)] at this; omega
  -- E1 = A1stage*2^159 + E0*v (cum 159). s1 gives bracket on e1 with this E1.
  -- stage 2: cum 159 -> 287, sh=0x80=128, P=2^121
  have s2 := horner_stage 0x9064d965e1c4863b73604e0ddbec53f9 (2^121) e1 v 159 0x80
    (0x9a036222e11aee18465042f8ea64c8 * 2^159 + (0xb9aacfad41060587203a79af0ebc * 2^29 + v) * v)
    hv (by norm_num) (by norm_num) he1lt (by norm_num)
    (by rw [pvd 121 126 128 119 (by norm_num)]; norm_num) (by norm_num) s1.1 s1.2
  set e2 := evmAdd 0x9064d965e1c4863b73604e0ddbec53f9 (evmShr 0x80 (evmMul e1 v)) with he2
  have he2lt : e2 < 2^129 := by
    have := (stage_bounds (c := 0x9064d965e1c4863b73604e0ddbec53f9) (prev := e1) (v := v)
      (P := 2^121) (V := 2^126) (sh := 0x80) he1lt hv (by norm_num) (by norm_num)
      (by rw [pvd 121 126 128 119 (by norm_num)]; norm_num)).2
    rw [pvd 121 126 128 119 (by norm_num)] at this; omega
  -- stage 3: cum 287 -> 421, sh=0x86=134, P=2^129
  have s3 := horner_stage 0x93f11e65781741b92fa7fc4f4fffcca2 (2^129) e2 v 287 0x86
    (0x9064d965e1c4863b73604e0ddbec53f9 * 2^287 +
      (0x9a036222e11aee18465042f8ea64c8 * 2^159 + (0xb9aacfad41060587203a79af0ebc * 2^29 + v) * v) * v)
    hv (by norm_num) (by norm_num) he2lt (by norm_num)
    (by rw [pvd 129 126 134 121 (by norm_num)]; norm_num) (by norm_num) s2.1 s2.2
  set e3 := evmAdd 0x93f11e65781741b92fa7fc4f4fffcca2 (evmShr 0x86 (evmMul e2 v)) with he3
  have he3lt : e3 < 2^129 := by
    have := (stage_bounds (c := 0x93f11e65781741b92fa7fc4f4fffcca2) (prev := e2) (v := v)
      (P := 2^129) (V := 2^126) (sh := 0x86) he2lt hv (by norm_num) (by norm_num)
      (by rw [pvd 129 126 134 121 (by norm_num)]; norm_num)).2
    rw [pvd 129 126 134 121 (by norm_num)] at this; omega
  -- stage 4: cum 421 -> 553, sh=0x84=132, P=2^129
  have s4 := horner_stage 0x4e14a45e8ec305e233e11b4174e214ac (2^129) e3 v 421 0x84
    (0x93f11e65781741b92fa7fc4f4fffcca2 * 2^421 +
      (0x9064d965e1c4863b73604e0ddbec53f9 * 2^287 +
        (0x9a036222e11aee18465042f8ea64c8 * 2^159 +
          (0xb9aacfad41060587203a79af0ebc * 2^29 + v) * v) * v) * v)
    hv (by norm_num) (by norm_num) he3lt (by norm_num)
    (by rw [pvd 129 126 132 123 (by norm_num)]; norm_num) (by norm_num) s3.1 s3.2
  -- assemble: evTree x = e4 (the stage-4 value), evNumV v = the cumulative E4.
  rw [hev]
  -- unfold evNumV to the same E4 expression
  show 2^553 * evmAdd 0x4e14a45e8ec305e233e11b4174e214ac (evmShr 0x84 (evmMul e3 v)) ≤ evNumV v ∧
    evNumV v < 2^553 * evmAdd 0x4e14a45e8ec305e233e11b4174e214ac (evmShr 0x84 (evmMul e3 v)) + 2 * 2^553
  unfold evNumV
  -- s4 has the right shape with cum+sh = 421+132 = 553
  have e553 : (421:Nat) + 0x84 = 553 := by norm_num
  rw [e553] at s4
  -- the E4 in s4 = A0*2^553 + E3*v matches evNumV's let-expansion
  constructor
  · have := s4.1
    -- s4.1: 2^553 * e4 <= A0 * 2^553 + E3 * v.  evNumV v = A0*2^553 + E3*v (after let).
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

/-- Runtime odd-Horner accumulator brackets the exact polynomial within `2` ulp at scale `2^530`. -/
theorem odTree_bracket {x : Nat} (hv : vTree x < 2 ^ 126) :
    2^530 * odTree x ≤ odNumV (vTree x) ∧ odNumV (vTree x) < 2^530 * odTree x + 2 * 2^530 := by
  have hod : odTree x =
      evmAdd 0x270a522f476182f119f08da0ba710a56 (evmShr 0x87 (evmMul
      (evmAdd 0xaf5662483c4ce783a9ef5fe025f42e9e (evmShr 0x7f (evmMul
      (evmAdd 0xad4506b00b1246c7e5b4fd33e1201b (evmShr 0x89 (evmMul
      (evmAdd 0xc926ddbf3830ca5561cc01585402d0 (evmShr 0x83 (evmMul
      0xdc07aff85e5bb5629d0fb64a84bb (vTree x)))) (vTree x)))) (vTree x)))) (vTree x))) := rfl
  set v := vTree x with hvdef
  -- the leading constant is its own (trivial) cumulative bracket at scale 2^0
  have hB4lo : 2^0 * 0xdc07aff85e5bb5629d0fb64a84bb ≤ 0xdc07aff85e5bb5629d0fb64a84bb := by norm_num
  have hB4hi : (0xdc07aff85e5bb5629d0fb64a84bb : Nat) < 2^0 * 0xdc07aff85e5bb5629d0fb64a84bb + 2 * 2^0 := by norm_num
  -- stage 1: cum 0 -> 131, sh=0x83=131, prev=B4<2^112
  have s1 := horner_stage 0xc926ddbf3830ca5561cc01585402d0 (2^112) 0xdc07aff85e5bb5629d0fb64a84bb v 0 0x83
    0xdc07aff85e5bb5629d0fb64a84bb hv (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [pvd 112 126 131 107 (by norm_num)]; norm_num) (by norm_num) hB4lo hB4hi
  set o1 := evmAdd 0xc926ddbf3830ca5561cc01585402d0 (evmShr 0x83 (evmMul 0xdc07aff85e5bb5629d0fb64a84bb v)) with ho1
  have ho1lt : o1 < 2^121 := by
    have := (stage_bounds (c := 0xc926ddbf3830ca5561cc01585402d0) (prev := 0xdc07aff85e5bb5629d0fb64a84bb) (v := v)
      (P := 2^112) (V := 2^126) (sh := 0x83) (by norm_num) hv (by norm_num) (by norm_num)
      (by rw [pvd 112 126 131 107 (by norm_num)]; norm_num)).2
    rw [pvd 112 126 131 107 (by norm_num)] at this; omega
  -- stage 2: cum 131 -> 268, sh=0x89=137, prev=o1<2^121
  have s2 := horner_stage 0xad4506b00b1246c7e5b4fd33e1201b (2^121) o1 v 131 0x89
    (0xc926ddbf3830ca5561cc01585402d0 * 2^131 + 0xdc07aff85e5bb5629d0fb64a84bb * v) hv (by norm_num) (by norm_num) ho1lt (by norm_num)
    (by rw [pvd 121 126 137 110 (by norm_num)]; norm_num) (by norm_num) s1.1 s1.2
  set o2 := evmAdd 0xad4506b00b1246c7e5b4fd33e1201b (evmShr 0x89 (evmMul o1 v)) with ho2
  have ho2lt : o2 < 2^121 := by
    have := (stage_bounds (c := 0xad4506b00b1246c7e5b4fd33e1201b) (prev := o1) (v := v)
      (P := 2^121) (V := 2^126) (sh := 0x89) ho1lt hv (by norm_num) (by norm_num)
      (by rw [pvd 121 126 137 110 (by norm_num)]; norm_num)).2
    rw [pvd 121 126 137 110 (by norm_num)] at this; omega
  -- stage 3: cum 268 -> 395, sh=0x7f=127, prev=o2<2^121
  have s3 := horner_stage 0xaf5662483c4ce783a9ef5fe025f42e9e (2^121) o2 v 268 0x7f
    (0xad4506b00b1246c7e5b4fd33e1201b * 2^268 +
      (0xc926ddbf3830ca5561cc01585402d0 * 2^131 + 0xdc07aff85e5bb5629d0fb64a84bb * v) * v) hv (by norm_num) (by norm_num) ho2lt (by norm_num)
    (by rw [pvd 121 126 127 120 (by norm_num)]; norm_num) (by norm_num) s2.1 s2.2
  set o3 := evmAdd 0xaf5662483c4ce783a9ef5fe025f42e9e (evmShr 0x7f (evmMul o2 v)) with ho3
  have ho3lt : o3 < 2^129 := by
    have := (stage_bounds (c := 0xaf5662483c4ce783a9ef5fe025f42e9e) (prev := o2) (v := v)
      (P := 2^121) (V := 2^126) (sh := 0x7f) ho2lt hv (by norm_num) (by norm_num)
      (by rw [pvd 121 126 127 120 (by norm_num)]; norm_num)).2
    rw [pvd 121 126 127 120 (by norm_num)] at this; omega
  -- stage 4: cum 395 -> 530, sh=0x87=135, prev=o3<2^129
  have s4 := horner_stage 0x270a522f476182f119f08da0ba710a56 (2^129) o3 v 395 0x87
    (0xaf5662483c4ce783a9ef5fe025f42e9e * 2^395 +
      (0xad4506b00b1246c7e5b4fd33e1201b * 2^268 +
        (0xc926ddbf3830ca5561cc01585402d0 * 2^131 + 0xdc07aff85e5bb5629d0fb64a84bb * v) * v) * v) hv (by norm_num) (by norm_num) ho3lt (by norm_num)
    (by rw [pvd 129 126 135 120 (by norm_num)]; norm_num) (by norm_num) s3.1 s3.2
  rw [hod]
  show 2^530 * evmAdd 0x270a522f476182f119f08da0ba710a56 (evmShr 0x87 (evmMul o3 v)) ≤ odNumV v ∧
    odNumV v < 2^530 * evmAdd 0x270a522f476182f119f08da0ba710a56 (evmShr 0x87 (evmMul o3 v)) + 2 * 2^530
  unfold odNumV
  have e530 : (395:Nat) + 0x87 = 530 := by norm_num
  rw [e530] at s4
  constructor
  · have := s4.1; convert this using 2 <;> ring
  · have := s4.2; convert this using 2 <;> ring

/-- info: 'ExpYul.odTree_bracket' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms odTree_bracket

/-! ## The below-clamp target bound (`RuntimeR0Bound.belowC`) -/

open ExpRealSpec
open Real

noncomputable section

/-- **Below the clamp boundary the target is under two output units.** For any word `x` whose signed
value is at or below the 0/1 clamp boundary `Cmask`, `E = 10¹⁸·exp(int256 x / 10²⁷) < 2`. -/
theorem belowC_target_lt_two {x : Nat} (hxle : int256 x ≤ int256 Cmask) :
    expRayToWadTarget (int256 x) < 2 := by
  unfold expRayToWadTarget
  have hCm : int256 Cmask = -41446531673892822312323846185 := int256_Cmask
  rw [hCm] at hxle
  have hRAY : (RAY : Real) = 10 ^ 27 := by unfold RAY; norm_num
  have hWAD : (WAD : Real) = 10 ^ 18 := by unfold WAD; norm_num
  have hxR : (int256 x : Real) ≤ -41446531673892822312323846185 := by exact_mod_cast hxle
  have harg : (int256 x : Real) / (RAY : Real) ≤ -41 := by
    rw [hRAY, div_le_iff₀ (by norm_num : (0:Real) < 10 ^ 27)]
    nlinarith [hxR]
  have hmono : Real.exp ((int256 x : Real) / (RAY : Real)) ≤ Real.exp (-41) :=
    Real.exp_le_exp.mpr harg
  have hexp41 : (5 * 10 ^ 17 : ℝ) < (Real.exp 1) ^ 41 := by
    have h2 : (5 * 10 ^ 17 : ℝ) < (2.7182818283 : ℝ) ^ 41 := by norm_num
    calc (5 * 10 ^ 17 : ℝ) < (2.7182818283 : ℝ) ^ 41 := h2
      _ < (Real.exp 1) ^ 41 := by gcongr; exact Real.exp_one_gt_d9
  have hen : Real.exp (-41) = ((Real.exp 1) ^ 41)⁻¹ := by
    rw [show (-41 : ℝ) = -((41 : ℕ) * (1 : ℝ)) by push_cast; ring, Real.exp_neg, Real.exp_nat_mul]
  have hp : (0 : ℝ) < (Real.exp 1) ^ 41 := by positivity
  have hexpneg41 : Real.exp (-41) < 2 / 10 ^ 18 := by
    rw [hen, inv_lt_iff_one_lt_mul₀ hp, div_mul_eq_mul_div, lt_div_iff₀ (by norm_num : (0:ℝ) < 10 ^ 18)]
    nlinarith [hexp41]
  rw [hWAD]
  calc (10 ^ 18 : ℝ) * Real.exp ((int256 x : Real) / (RAY : Real))
      ≤ 10 ^ 18 * Real.exp (-41) := by
        nlinarith [hmono, Real.exp_pos ((int256 x : Real) / (RAY : Real))]
    _ < 10 ^ 18 * (2 / 10 ^ 18) := by nlinarith [hexpneg41]
    _ = 2 := by norm_num

/-- info: 'ExpYul.belowC_target_lt_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms belowC_target_lt_two

end

end ExpYul

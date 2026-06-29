import ExpProof.Mono.Stages

/-!
# The reciprocal-symmetric quotient stage

From the stage bounds this file assembles the closing quotient `r0 = exp(t)·2^126`:

* `tod = ⌊t·Od / 2^128⌋` transported to `Int`, with `|tod| < 2^125`;
* the numerator `num = ev + tod` and denominator `den = ev − tod` are strictly positive (the
  reduced argument keeps `|tod|` well below `ev`);
* `r0 = sdiv(2^126·num, den)` is strictly positive and below `2^128`.

These give the range and nonnegativity obligations directly, and (via the cross-multiplication
identity) reduce the within-octave monotonicity to a fact about `tod·ev`.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

/-! ## `tod = t·Od` in Q87 -/

/-- `tod` transported to `Int`: a signed floor with `|tod| < 2^125`. The product `t·Od` fits a word
(`|t| < 2^127`, `Od < 2^126`, so `|t·Od| < 2^253`). -/
theorem todTree_bound {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    -(2 ^ 125 : Int) ≤ int256 (todTree x) ∧ int256 (todTree x) < 2 ^ 125 ∧
      (2 ^ 128 : Int) * int256 (todTree x) ≤ int256 (tTree x) * (odTree x : Int) ∧
      int256 (tTree x) * (odTree x : Int) <
        (2 ^ 128 : Int) * int256 (todTree x) + 2 ^ 128 := by
  obtain ⟨htlo, hthi⟩ := tTree_bound hx hC hC0
  obtain ⟨_, hvlt⟩ := vTree_eq hx hC hC0
  have hodlt : odTree x < 2 ^ 126 := odTree_lt hvlt
  have htw : tTree x < 2 ^ 256 := by unfold tTree; exact evmSar_lt _ _
  have hodw : odTree x < 2 ^ 256 := by unfold odTree; exact evmAdd_lt _ _
  set t := int256 (tTree x) with htdef
  -- od is a small nonnegative word
  have hodi : int256 (odTree x) = (odTree x : Int) := int256_of_lt (by
    have : (2:Nat)^126 < 2 ^ 255 := by norm_num
    omega)
  have hod_nn : 0 ≤ (odTree x : Int) := by positivity
  have hod_ub : (odTree x : Int) < 2 ^ 126 := by exact_mod_cast hodlt
  -- the product t·od fits
  have hp127 : (2:Int)^127 = 170141183460469231731687303715884105728 := by norm_num
  have hp126 : (2:Int)^126 = 85070591730234615865843651857942052864 := by norm_num
  have hp253 : (2:Int)^253 = 14474011154664524427946373126085988481658748083205070504932198000989141204992 := by norm_num
  have hp255 : (2:Int)^255 = 57896044618658097711785492504343953926634992332820282019728792003956564819968 := by norm_num
  have hprod_lt : t * (odTree x : Int) < 2 ^ 253 := by
    rw [hp127] at htlo hthi; rw [hp126] at hod_ub; rw [hp253]; nlinarith [htlo, hthi, hod_nn, hod_ub]
  have hprod_gt : -(2 ^ 253 : Int) < t * (odTree x : Int) := by
    rw [hp127] at htlo hthi; rw [hp126] at hod_ub; rw [hp253]; nlinarith [htlo, hthi, hod_nn, hod_ub]
  -- transport the multiply
  have hmul : int256 (evmMul (tTree x) (odTree x)) = t * (odTree x : Int) := by
    have := evmMul_transport htw hodw (by rw [hodi]; simp only [ipow255]; nlinarith [hprod_gt, hp253, hp255])
      (by rw [hodi]; simp only [ipow255]; nlinarith [hprod_lt, hp253, hp255])
    rw [hodi] at this; exact this
  have hmul_lt : evmMul (tTree x) (odTree x) < 2 ^ 256 := evmMul_lt _ _
  -- the `sar 128` floor sandwich
  obtain ⟨_, hsl, hsh⟩ := evmSar_sandwich (s := 0x80) (by norm_num) hmul_lt
  rw [hmul] at hsl hsh
  have hsh128 : (2:Int) ^ 0x80 = 2 ^ 128 := by norm_num
  rw [hsh128] at hsl hsh
  have htodeq : int256 (todTree x) = int256 (evmSar 0x80 (evmMul (tTree x) (odTree x))) := by
    unfold todTree; rfl
  rw [htodeq]
  refine ⟨?_, ?_, hsl, hsh⟩
  · -- lower bound: 2^128·tod ≤ t·od and t·od > -2^253 ⇒ tod > -2^125
    nlinarith [hsl, hprod_gt, hp253]
  · -- upper bound: t·od < 2^128·tod + 2^128 and t·od < 2^253 ⇒ tod < 2^125
    nlinarith [hsh, hprod_lt, hp253]

/-! ## Numerator and denominator -/

/-- Abstract numerator/denominator positivity: stated over opaque words `E` (the even accumulator)
and `TD` (the signed `t·Od` shift) with their bounds, so the deep Horner tree is never forced. -/
theorem numden_pos_of {E TD : Nat} (hevw : E < 2 ^ 256) (htodw : TD < 2 ^ 256)
    (hev_lo : (103786963415199049567855548359006885036 : Int) ≤ (E : Int))
    (hev_hi : (E : Int) < 2 ^ 127)
    (htod_lo : -(42535295865117307932921825928971026432 : Int) ≤ int256 TD)
    (htod_hi : int256 TD < 42535295865117307932921825928971026432) :
    int256 (evmAdd E TD) = (E : Int) + int256 TD ∧
      int256 (evmSub E TD) = (E : Int) - int256 TD ∧
      0 < (E : Int) + int256 TD ∧
      0 < (E : Int) - int256 TD := by
  have hevi : int256 E = (E : Int) := int256_of_lt (by
    have : (2:Nat)^127 < 2 ^ 255 := by norm_num
    omega)
  have hp127 : (E : Int) < 170141183460469231731687303715884105728 := by
    rw [show (170141183460469231731687303715884105728 : Int) = 2 ^ 127 by norm_num]; exact hev_hi
  have hadd : int256 (evmAdd E TD) = (E : Int) + int256 TD := by
    have := evmAdd_transport hevw htodw
      (by rw [hevi]; simp only [ipow255]; omega)
      (by rw [hevi]; simp only [ipow255]; omega)
    rw [hevi] at this; exact this
  have hsub : int256 (evmSub E TD) = (E : Int) - int256 TD := by
    have := evmSub_transport hevw htodw
      (by rw [hevi]; simp only [ipow255]; omega)
      (by rw [hevi]; simp only [ipow255]; omega)
    rw [hevi] at this; exact this
  exact ⟨hadd, hsub, by omega, by omega⟩

/-- `num = ev + tod` and `den = ev − tod`, transported to `Int`, are both strictly positive: the
even accumulator dominates `|tod|`. -/
theorem numden_pos {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    int256 (evmAdd (evTree x) (todTree x)) = (evTree x : Int) + int256 (todTree x) ∧
      int256 (evmSub (evTree x) (todTree x)) = (evTree x : Int) - int256 (todTree x) ∧
      0 < (evTree x : Int) + int256 (todTree x) ∧
      0 < (evTree x : Int) - int256 (todTree x) := by
  obtain ⟨_, hvlt⟩ := vTree_eq hx hC hC0
  obtain ⟨hev_lo, hev_hi⟩ := evTree_facts hvlt
  obtain ⟨htod_lo, htod_hi, _, _⟩ := todTree_bound hx hC hC0
  have hevw : evTree x < 2 ^ 256 := by unfold evTree; exact evmAdd_lt _ _
  have htodw : todTree x < 2 ^ 256 := by unfold todTree; exact evmSar_lt _ _
  refine numden_pos_of hevw htodw ?_ ?_ ?_ ?_
  · have : (0x4e14a45e8ec305e233e11b4174e214ac : Int) ≤ (evTree x : Int) := by exact_mod_cast hev_lo
    rw [show (0x4e14a45e8ec305e233e11b4174e214ac : Int) = 103786963415199049567855548359006885036 by norm_num] at this
    exact this
  · have : (evTree x : Int) < (2 ^ 127 : Nat) := by exact_mod_cast hev_hi
    rw [show ((2 ^ 127 : Nat) : Int) = 2 ^ 127 by norm_num] at this; exact this
  · rw [show (42535295865117307932921825928971026432 : Int) = 2 ^ 125 by norm_num]; exact htod_lo
  · rw [show (42535295865117307932921825928971026432 : Int) = 2 ^ 125 by norm_num]; exact htod_hi

/-! ## The closing quotient `r0 = exp(t)·2^126` -/

/-- Abstract quotient bounds over opaque numerator/denominator words. `r0 = ⌊2^126·N/D⌋` lies in
`[1, 2^128)`: the dividend `2^126·N` fits a word, `D ≤ 2^126·N` keeps the quotient `≥ 1`, and
`N < 4·D` keeps it below `2^128`. -/
theorem r0Tree_bounds_of {N D : Nat} (hN : N < 2 ^ 128) (hDlt : D < 2 ^ 128) (hD : D < 2 ^ 256)
    (hDi : int256 D = (D : Int))
    (hNpos : 0 < (N : Int)) (hDpos : 0 < (D : Int))
    (hNlo : 2 ^ 125 ≤ N)
    (hND : (N : Int) < 4 * (D : Int)) :
    1 ≤ int256 (evmSdiv (evmShl 0x7e N) D) ∧ int256 (evmSdiv (evmShl 0x7e N) D) < 2 ^ 128 := by
  -- shl(126, N) = N·2^126 (fits: N < 2^128 ⇒ N·2^126 < 2^254)
  have hshl : evmShl 0x7e N = N * 2 ^ 0x7e := by
    refine evmShl_eq (by norm_num) ?_
    have : N * 2 ^ 0x7e < 2 ^ 128 * 2 ^ 0x7e := by
      have hp : 0 < 2 ^ 0x7e := Nat.two_pow_pos _
      exact (Nat.mul_lt_mul_right hp).mpr hN
    rw [show (2:Nat) ^ 128 * 2 ^ 0x7e = 2 ^ 254 by rw [← Nat.pow_add]] at this
    omega
  have hNpos' : 0 < N := by exact_mod_cast hNpos
  have hShlLt254 : N * 2 ^ 0x7e < 2 ^ 254 := by
    have hp : 0 < 2 ^ 0x7e := Nat.two_pow_pos _
    calc N * 2 ^ 0x7e < 2 ^ 128 * 2 ^ 0x7e := (Nat.mul_lt_mul_right hp).mpr hN
      _ = 2 ^ 254 := by rw [← Nat.pow_add]
  have hShlLt255 : N * 2 ^ 0x7e < 2 ^ 255 := by
    have : (2:Nat) ^ 254 < 2 ^ 255 := by norm_num
    omega
  have hdivpos : 0 < int256 (evmShl 0x7e N) := by
    rw [hshl, int256_of_lt hShlLt255]
    have hpos : 0 < N * 2 ^ 0x7e := Nat.mul_pos hNpos' (Nat.two_pow_pos _)
    exact_mod_cast hpos
  -- both operands positive ⇒ sdiv = floor division
  have hshl_lt : evmShl 0x7e N < 2 ^ 256 := evmShl_lt _ _
  rw [evmSdiv_pos_pos hshl_lt hD (le_of_lt hdivpos) (by rw [hDi]; exact hDpos)]
  -- the toNat magnitudes
  have hshl_nat : evmShl 0x7e N = N * 2 ^ 0x7e := hshl
  have hN_toNat : (int256 (evmShl 0x7e N)).toNat = N * 2 ^ 0x7e := by
    rw [hshl, int256_of_lt hShlLt255, Int.toNat_natCast]
  have hD_toNat : (int256 D).toNat = D := by rw [hDi, Int.toNat_natCast]
  rw [hN_toNat, hD_toNat]
  set q := N * 2 ^ 0x7e / D with hq
  have hDnat_pos : 0 < D := by exact_mod_cast hDpos
  have hNnat_pos : 0 < N := by exact_mod_cast hNpos
  have hq_lt : q < 2 ^ 128 := by
    rw [hq]
    rw [Nat.div_lt_iff_lt_mul hDnat_pos]
    -- N·2^126 < 2^128·D ⟺ N < 4·D
    have hND' : N < 4 * D := by
      have : (N : Int) < 4 * (D : Int) := hND
      have h4 : ((4 * D : Nat) : Int) = 4 * (D : Int) := by push_cast; ring
      rw [← h4] at this; exact_mod_cast this
    calc N * 2 ^ 0x7e < 4 * D * 2 ^ 0x7e := by
            have hp : 0 < 2 ^ 0x7e := Nat.two_pow_pos _
            exact (Nat.mul_lt_mul_right hp).mpr hND'
      _ = 2 ^ 128 * D := by
            rw [show (4:Nat) * D * 2 ^ 0x7e = (4 * 2 ^ 0x7e) * D by ring,
              show (4:Nat) * 2 ^ 0x7e = 2 ^ 128 by norm_num]
  have hq_ge : 1 ≤ q := by
    rw [hq, Nat.le_div_iff_mul_le hDnat_pos, Nat.one_mul]
    -- D < 2^128 ≤ 2^125·2^126 ≤ N·2^126
    have h1 : (2:Nat) ^ 128 ≤ 2 ^ 125 * 2 ^ 0x7e := by
      rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
    have h2 : (2:Nat) ^ 125 * 2 ^ 0x7e ≤ N * 2 ^ 0x7e := Nat.mul_le_mul_right _ hNlo
    omega
  exact ⟨by exact_mod_cast hq_ge, by
    have : (q : Int) < 2 ^ 128 := by exact_mod_cast hq_lt
    simpa using this⟩

/-- For a canonical word with nonnegative signed value, the signed value is the Nat value (and the
word lies in the lower half). -/
theorem int256_eq_of_nonneg {w : Nat} (hw : w < 2 ^ 256) (hnn : 0 ≤ int256 w) :
    int256 w = (w : Int) ∧ w < 2 ^ 255 := by
  unfold int256 at hnn ⊢
  split at hnn
  · rename_i h; exact ⟨if_pos h, h⟩
  · rename_i h; exfalso; simp only [ipow256] at hnn; have : (w : Int) < 2 ^ 256 := by exact_mod_cast hw
    simp only [ipow256] at this; omega

/-- Abstract `r0` bounds: `1 ≤ r0 < 2^128` over opaque even/odd words `E`, `TD` with their bounds.
`r0 = sdiv(2^126·(E+TD), E−TD)`; the numerator and denominator are positive and the quotient lands
in `[1, 2^128)` (the reduced argument keeps `exp(t) ∈ [1/√2, √2)`). -/
theorem r0Tree_bounds_ofEvTod {E TD : Nat} (hevw : E < 2 ^ 256) (htodw : TD < 2 ^ 256)
    (hev_lo : (103786963415199049567855548359006885036 : Int) ≤ (E : Int))
    (hev_hi : (E : Int) < 2 ^ 127)
    (htod_lo : -(42535295865117307932921825928971026432 : Int) ≤ int256 TD)
    (htod_hi : int256 TD < 42535295865117307932921825928971026432) :
    1 ≤ int256 (evmSdiv (evmShl 0x7e (evmAdd E TD)) (evmSub E TD)) ∧
      int256 (evmSdiv (evmShl 0x7e (evmAdd E TD)) (evmSub E TD)) < 2 ^ 128 := by
  obtain ⟨hadd, hsub, hnum_pos, hden_pos⟩ := numden_pos_of hevw htodw hev_lo hev_hi htod_lo htod_hi
  have hNwlt : evmAdd E TD < 2 ^ 256 := evmAdd_lt _ _
  have hDwlt : evmSub E TD < 2 ^ 256 := evmSub_lt _ _
  -- numeric forms
  have h128 : (2:Int)^128 = 340282366920938463463374607431768211456 := by norm_num
  have h127 : (2:Int)^127 = 170141183460469231731687303715884105728 := by norm_num
  rw [h127] at hev_hi
  -- canonical Nat values for num and den
  obtain ⟨hNi, hNlt255⟩ := int256_eq_of_nonneg hNwlt (by rw [hadd]; omega)
  obtain ⟨hDi, hDlt255⟩ := int256_eq_of_nonneg hDwlt (by rw [hsub]; omega)
  -- numerator and denominator Nat bounds
  have hNlt128 : evmAdd E TD < 2 ^ 128 := by
    have : ((evmAdd E TD : Nat) : Int) < 2 ^ 128 := by rw [← hNi, hadd, h128]; omega
    exact_mod_cast this
  have hDlt128 : evmSub E TD < 2 ^ 128 := by
    have : ((evmSub E TD : Nat) : Int) < 2 ^ 128 := by rw [← hDi, hsub, h128]; omega
    exact_mod_cast this
  have hNlo : 2 ^ 125 ≤ evmAdd E TD := by
    have : (2 ^ 125 : Int) ≤ ((evmAdd E TD : Nat) : Int) := by
      rw [← hNi, hadd, show (2:Int)^125 = 42535295865117307932921825928971026432 by norm_num]; omega
    exact_mod_cast this
  have hND : ((evmAdd E TD : Nat) : Int) < 4 * ((evmSub E TD : Nat) : Int) := by
    rw [← hNi, ← hDi, hadd, hsub]; omega
  have hNpos : 0 < ((evmAdd E TD : Nat) : Int) := by rw [← hNi, hadd]; omega
  have hDpos : 0 < ((evmSub E TD : Nat) : Int) := by rw [← hDi, hsub]; omega
  exact r0Tree_bounds_of hNlt128 hDlt128 hDwlt hDi hNpos hDpos hNlo hND

/-- `1 ≤ r0Tree x < 2^128` on the meaningful region. -/
theorem r0Tree_bounds {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    1 ≤ int256 (r0Tree x) ∧ int256 (r0Tree x) < 2 ^ 128 := by
  obtain ⟨_, hvlt⟩ := vTree_eq hx hC hC0
  obtain ⟨hev_lo, hev_hi⟩ := evTree_facts hvlt
  obtain ⟨htod_lo, htod_hi, _, _⟩ := todTree_bound hx hC hC0
  have hr0 : r0Tree x =
      evmSdiv (evmShl 0x7e (evmAdd (evTree x) (todTree x))) (evmSub (evTree x) (todTree x)) := rfl
  rw [hr0]
  have hevw : evTree x < 2 ^ 256 := by unfold evTree; exact evmAdd_lt _ _
  have htodw : todTree x < 2 ^ 256 := by unfold todTree; exact evmSar_lt _ _
  refine r0Tree_bounds_ofEvTod hevw htodw ?_ ?_ ?_ ?_
  · have : (0x4e14a45e8ec305e233e11b4174e214ac : Int) ≤ (evTree x : Int) := by exact_mod_cast hev_lo
    rw [show (0x4e14a45e8ec305e233e11b4174e214ac : Int) = 103786963415199049567855548359006885036 by norm_num] at this
    exact this
  · have : (evTree x : Int) < (2 ^ 127 : Nat) := by exact_mod_cast hev_hi
    rw [show ((2 ^ 127 : Nat) : Int) = 2 ^ 127 by norm_num] at this; exact this
  · rw [show (42535295865117307932921825928971026432 : Int) = 2 ^ 125 by norm_num]; exact htod_lo
  · rw [show (42535295865117307932921825928971026432 : Int) = 2 ^ 125 by norm_num]; exact htod_hi

end ExpYul

import ExpProof.Mono.Stages

/-!
# The reciprocal-symmetric quotient stage

From the stage bounds this file assembles the closing quotient `r0 = ⌊scaleQ67·exp(t)⌋`:

* `tod = ⌊t·Od / 2^129⌋` transported to `Int`, with `|tod| < 2^126`;
* the numerator `num = ev + tod` and denominator `den = ev − tod` are strictly positive (the
  reduced argument keeps `|tod|` well below `ev`);
* `r0 = div(2^126·num, den)` — a plain `Nat` floor division — is at least `2^123` and below
  `2^128`.

These give the range and nonnegativity obligations directly, and (via the cross-multiplication
identity) reduce the within-octave monotonicity to a fact about `tod·ev`.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

/-- A word whose signed transport is nonnegative is its own `Int` cast and lies below `2 ^ 255`. -/
theorem int256_eq_of_nonneg {w : Nat} (hw : w < 2 ^ 256) (hnn : 0 ≤ int256 w) :
    int256 w = (w : Int) ∧ w < 2 ^ 255 := by
  unfold int256 at hnn ⊢
  by_cases h : w < 2 ^ 255
  · rw [if_pos h]
    exact ⟨rfl, h⟩
  · rw [if_neg h] at hnn
    exfalso
    omega

/-! ## `tod = t·Od` in Q88 -/

/-- `tod` transported to `Int`: a signed floor with `|tod| < 2^126`. The product `t·Od` fits a word
(`|t| < 2.4·10³⁸`, `Od < 5·2^125`, so `|t·Od| < 29·2^250`). -/
theorem todTree_bound_wide {x : Nat} (hx : x < 2 ^ 256) (hW : WideRegion x) :
    -(2 ^ 126 : Int) ≤ int256 (todTree x) ∧ int256 (todTree x) < 2 ^ 126 ∧
      (2 ^ 129 : Int) * int256 (todTree x) ≤ int256 (tTree x) * (odTree x : Int) ∧
      int256 (tTree x) * (odTree x : Int) <
        (2 ^ 129 : Int) * int256 (todTree x) + 2 ^ 129 := by
  obtain ⟨htlo, hthi⟩ := tTree_bound_sharp_wide hx hW
  obtain ⟨_, hvlt⟩ := vTree_eq_wide hx hW
  have hodlt : odTree x < 5 * 2 ^ 125 := odTree_lt hvlt
  have htw : tTree x < 2 ^ 256 := by unfold tTree; exact evmSar_lt _ _
  have hodw : odTree x < 2 ^ 256 := by unfold odTree; exact evmAdd_lt _ _
  set t := int256 (tTree x) with htdef
  -- od is a small nonnegative word
  have hodi : int256 (odTree x) = (odTree x : Int) := int256_of_lt (by
    have : 5 * 2 ^ 125 < (2:Nat) ^ 255 := by norm_num
    omega)
  have hod_nn : 0 ≤ (odTree x : Int) := by positivity
  have hod_ub : (odTree x : Int) < 5 * 2 ^ 125 := by exact_mod_cast hodlt
  -- the product t·od fits
  have hp126 : (2:Int)^126 = 85070591730234615865843651857942052864 := by norm_num
  have hp252 : (29:Int) * 2^250 = 52468290435658901051305602582061708246012961801618380580379217753585636868096 := by norm_num
  have hp255 : (2:Int)^255 = 57896044618658097711785492504343953926634992332820282019728792003956564819968 := by norm_num
  have hprod_lt : t * (odTree x : Int) < 29 * 2 ^ 250 := by
    rw [show (5:Int) * 2 ^ 125 = 212676479325586539664609129644855132160 by norm_num] at hod_ub
    rw [hp252]; nlinarith [htlo, hthi, hod_nn, hod_ub]
  have hprod_gt : -(29 * 2 ^ 250 : Int) < t * (odTree x : Int) := by
    rw [show (5:Int) * 2 ^ 125 = 212676479325586539664609129644855132160 by norm_num] at hod_ub
    rw [hp252]; nlinarith [htlo, hthi, hod_nn, hod_ub]
  -- transport the multiply
  have hmul : int256 (evmMul (tTree x) (odTree x)) = t * (odTree x : Int) := by
    have := evmMul_transport htw hodw (by rw [hodi]; simp only [ipow255]; nlinarith [hprod_gt, hp252, hp255])
      (by rw [hodi]; simp only [ipow255]; nlinarith [hprod_lt, hp252, hp255])
    rw [hodi] at this; exact this
  have hmul_lt : evmMul (tTree x) (odTree x) < 2 ^ 256 := evmMul_lt _ _
  -- the `sar 128` floor sandwich
  obtain ⟨_, hsl, hsh⟩ := evmSar_sandwich (s := 0x81) (by norm_num) hmul_lt
  rw [hmul] at hsl hsh
  have hsh129 : (2:Int) ^ 0x81 = 2 ^ 129 := by norm_num
  rw [hsh129] at hsl hsh
  have htodeq : int256 (todTree x) = int256 (evmSar 0x81 (evmMul (tTree x) (odTree x))) := by
    unfold todTree; rfl
  rw [htodeq]
  refine ⟨?_, ?_, hsl, hsh⟩
  · -- lower bound: 2^129·tod ≤ t·od and t·od > -29·2^250 ⇒ tod > -2^126
    nlinarith [hsl, hprod_gt, hp252]
  · -- upper bound: t·od < 2^129·tod + 2^129 and t·od < 29·2^250 ⇒ tod < 2^126
    nlinarith [hsh, hprod_lt, hp252]

theorem todTree_bound {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    -(2 ^ 126 : Int) ≤ int256 (todTree x) ∧ int256 (todTree x) < 2 ^ 126 ∧
      (2 ^ 129 : Int) * int256 (todTree x) ≤ int256 (tTree x) * (odTree x : Int) ∧
      int256 (tTree x) * (odTree x : Int) <
        (2 ^ 129 : Int) * int256 (todTree x) + 2 ^ 129 :=
  todTree_bound_wide hx (wideRegion_of_wad hC hC0)

/-! ## Numerator and denominator -/

/-- Abstract numerator/denominator positivity: stated over opaque words `E` (the even accumulator)
and `TD` (the signed `t·Od` shift) with their bounds, so the deep Horner tree is never forced. -/
theorem numden_pos_of {E TD : Nat} (hevw : E < 2 ^ 256) (htodw : TD < 2 ^ 256)
    (hev_lo : (415147853590918758559635130244235626256 : Int) ≤ (E : Int))
    (hev_hi : (E : Int) < 3 * 2 ^ 127)
    (htod_lo : -(85070591730234615865843651857942052864 : Int) ≤ int256 TD)
    (htod_hi : int256 TD < 85070591730234615865843651857942052864) :
    int256 (evmAdd E TD) = (E : Int) + int256 TD ∧
      int256 (evmSub E TD) = (E : Int) - int256 TD ∧
      0 < (E : Int) + int256 TD ∧
      0 < (E : Int) - int256 TD := by
  have hevi : int256 E = (E : Int) := int256_of_lt (by
    have hEc : (E : Int) < ((2 ^ 255 : Nat) : Int) := by
      have : (3 : Int) * 2 ^ 127 < ((2 ^ 255 : Nat) : Int) := by norm_num
      linarith [hev_hi]
    exact_mod_cast hEc)
  have hp127 : (E : Int) < 510423550381407695195061911147652317184 := by
    rw [show (510423550381407695195061911147652317184 : Int) = 3 * 2 ^ 127 by norm_num]; exact hev_hi
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
theorem numden_pos_wide {x : Nat} (hx : x < 2 ^ 256) (hW : WideRegion x) :
    int256 (evmAdd (evTree x) (todTree x)) = (evTree x : Int) + int256 (todTree x) ∧
      int256 (evmSub (evTree x) (todTree x)) = (evTree x : Int) - int256 (todTree x) ∧
      0 < (evTree x : Int) + int256 (todTree x) ∧
      0 < (evTree x : Int) - int256 (todTree x) := by
  obtain ⟨_, hvlt⟩ := vTree_eq_wide hx hW
  obtain ⟨hev_lo, hev_hi⟩ := evTree_facts hvlt
  obtain ⟨htod_lo, htod_hi, _, _⟩ := todTree_bound_wide hx hW
  have hevw : evTree x < 2 ^ 256 := by unfold evTree; exact evmAdd_lt _ _
  have htodw : todTree x < 2 ^ 256 := by unfold todTree; exact evmSar_lt _ _
  refine numden_pos_of hevw htodw ?_ ?_ ?_ ?_
  · have : (0x1385291795942d41ba5fd317688e18710 : Int) ≤ (evTree x : Int) := by exact_mod_cast hev_lo
    rw [show (0x1385291795942d41ba5fd317688e18710 : Int) = 415147853590918758559635130244235626256 by norm_num] at this
    exact this
  · have : (evTree x : Int) < ((3 * 2 ^ 127 : Nat) : Int) := by exact_mod_cast hev_hi
    rw [show ((3 * 2 ^ 127 : Nat) : Int) = 3 * 2 ^ 127 by norm_num] at this; exact this
  · rw [show (85070591730234615865843651857942052864 : Int) = 2 ^ 126 by norm_num]; exact htod_lo
  · rw [show (85070591730234615865843651857942052864 : Int) = 2 ^ 126 by norm_num]; exact htod_hi

theorem numden_pos {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    int256 (evmAdd (evTree x) (todTree x)) = (evTree x : Int) + int256 (todTree x) ∧
      int256 (evmSub (evTree x) (todTree x)) = (evTree x : Int) - int256 (todTree x) ∧
      0 < (evTree x : Int) + int256 (todTree x) ∧
      0 < (evTree x : Int) - int256 (todTree x) :=
  numden_pos_wide hx (wideRegion_of_wad hC hC0)

/-! ## The runtime quotient `r0 = ⌊(10¹⁸·2⁶⁷)·num/den⌋` -/

/-- Abstract scaled-quotient bounds over opaque numerator/denominator words: `⌊scaleQ67·N/D⌋`
lies in `[2^124, 2^130)`. The dividend `scaleQ67·N` fits a word (`N < 2^129`,
`scaleQ67 < 2^127`); `2^124·D < 2^253 ≤ scaleQ67·N` keeps the quotient `≥ 2^124` (comfortably
clearing the closing stage's `r0 > MARGIN`), and `N < 4·D` with `4·scaleQ67 ≤ 2^130` keeps it
below `2^130`. -/
theorem r0Tree_bounds_of {N D : Nat} (hN : N < 2 ^ 129) (hDlt : D < 2 ^ 129) (hD : D < 2 ^ 256)
    (hDi : int256 D = (D : Int))
    (hNpos : 0 < (N : Int)) (hDpos : 0 < (D : Int))
    (hNlo : 2 ^ 127 ≤ N)
    (hND : (N : Int) < 4 * (D : Int)) :
    2 ^ 124 ≤ int256 (evmDiv (evmMul scaleQ67 N) D) ∧
      int256 (evmDiv (evmMul scaleQ67 N) D) < 2 ^ 130 := by
  have hNw : N < 2 ^ 256 := by
    have : (2:Nat) ^ 128 < 2 ^ 256 := by norm_num
    omega
  have hsw : scaleQ67 < 2 ^ 256 := by unfold scaleQ67; norm_num
  have hfit : scaleQ67 * N < 2 ^ 256 := by
    have h1 : scaleQ67 * N ≤ scaleQ67 * 2 ^ 129 := Nat.mul_le_mul_left _ (le_of_lt hN)
    have h2 : scaleQ67 * 2 ^ 129 < 2 ^ 256 := by unfold scaleQ67; norm_num
    omega
  have hmul : evmMul scaleQ67 N = scaleQ67 * N := evmMul_eq_nat hsw hNw hfit
  have hDnat_pos : 0 < D := by exact_mod_cast hDpos
  have hdiv : evmDiv (evmMul scaleQ67 N) D = scaleQ67 * N / D := by
    rw [hmul, evmDiv_eq hfit hD (by omega)]
  set q := scaleQ67 * N / D with hq
  have hspos : 0 < scaleQ67 := by unfold scaleQ67; norm_num
  have hq_lt : q < 2 ^ 130 := by
    rw [hq, Nat.div_lt_iff_lt_mul hDnat_pos]
    have hND' : N < 4 * D := by
      have h4 : ((4 * D : Nat) : Int) = 4 * (D : Int) := by push_cast; ring
      rw [← h4] at hND; exact_mod_cast hND
    have h1 : scaleQ67 * N < scaleQ67 * (4 * D) := (Nat.mul_lt_mul_left hspos).mpr hND'
    have h2 : scaleQ67 * (4 * D) = (4 * scaleQ67) * D := by ring
    have h3 : (4 * scaleQ67) * D ≤ 2 ^ 130 * D :=
      Nat.mul_le_mul_right _ (by unfold scaleQ67; norm_num)
    omega
  have hq_ge : 2 ^ 124 ≤ q := by
    rw [hq, Nat.le_div_iff_mul_le hDnat_pos]
    have h1 : (2:Nat) ^ 124 * D ≤ 2 ^ 124 * 2 ^ 129 := Nat.mul_le_mul_left _ (le_of_lt hDlt)
    have h2 : (2:Nat) ^ 124 * 2 ^ 129 ≤ scaleQ67 * 2 ^ 127 := by unfold scaleQ67; norm_num
    have h3 : scaleQ67 * 2 ^ 127 ≤ scaleQ67 * N := Nat.mul_le_mul_left _ hNlo
    omega
  have hqi : int256 (evmDiv (evmMul scaleQ67 N) D) = (q : Int) := by
    rw [hdiv]
    exact int256_of_lt (by
      have : (2:Nat) ^ 130 < 2 ^ 255 := by norm_num
      omega)
  rw [hqi]
  exact ⟨by exact_mod_cast hq_ge, by exact_mod_cast hq_lt⟩

/-- Abstract runtime `r0` bounds over opaque even/odd words: `2^124 ≤ r0 < 2^130` with
`r0 = div(scaleQ67·(E+TD), E−TD)`. -/
theorem r0Tree_bounds_ofEvTod {E TD : Nat} (hevw : E < 2 ^ 256) (htodw : TD < 2 ^ 256)
    (hev_lo : (415147853590918758559635130244235626256 : Int) ≤ (E : Int))
    (hev_hi : (E : Int) < 3 * 2 ^ 127)
    (htod_lo : -(85070591730234615865843651857942052864 : Int) ≤ int256 TD)
    (htod_hi : int256 TD < 85070591730234615865843651857942052864) :
    2 ^ 124 ≤ int256 (evmDiv (evmMul scaleQ67 (evmAdd E TD)) (evmSub E TD)) ∧
      int256 (evmDiv (evmMul scaleQ67 (evmAdd E TD)) (evmSub E TD)) < 2 ^ 130 := by
  obtain ⟨hadd, hsub, hnum_pos, hden_pos⟩ := numden_pos_of hevw htodw hev_lo hev_hi htod_lo htod_hi
  have hNwlt : evmAdd E TD < 2 ^ 256 := evmAdd_lt _ _
  have hDwlt : evmSub E TD < 2 ^ 256 := evmSub_lt _ _
  have h128 : (2:Int)^129 = 680564733841876926926749214863536422912 := by norm_num
  have h127 : (3:Int) * 2 ^ 127 = 510423550381407695195061911147652317184 := by norm_num
  rw [h127] at hev_hi
  obtain ⟨hNi, hNlt255⟩ := int256_eq_of_nonneg hNwlt (by rw [hadd]; omega)
  obtain ⟨hDi, hDlt255⟩ := int256_eq_of_nonneg hDwlt (by rw [hsub]; omega)
  have hNlt128 : evmAdd E TD < 2 ^ 129 := by
    have : ((evmAdd E TD : Nat) : Int) < 2 ^ 129 := by rw [← hNi, hadd, h128]; omega
    exact_mod_cast this
  have hDlt128 : evmSub E TD < 2 ^ 129 := by
    have : ((evmSub E TD : Nat) : Int) < 2 ^ 129 := by rw [← hDi, hsub, h128]; omega
    exact_mod_cast this
  have hNlo : 2 ^ 127 ≤ evmAdd E TD := by
    have : (2 ^ 127 : Int) ≤ ((evmAdd E TD : Nat) : Int) := by
      rw [← hNi, hadd, show (2:Int)^127 = 170141183460469231731687303715884105728 by norm_num]
      omega
    exact_mod_cast this
  have hND : ((evmAdd E TD : Nat) : Int) < 4 * ((evmSub E TD : Nat) : Int) := by
    rw [← hNi, ← hDi, hadd, hsub]; omega
  have hNpos : 0 < ((evmAdd E TD : Nat) : Int) := by rw [← hNi, hadd]; omega
  have hDpos : 0 < ((evmSub E TD : Nat) : Int) := by rw [← hDi, hsub]; omega
  exact r0Tree_bounds_of hNlt128 hDlt128 hDwlt hDi hNpos hDpos hNlo hND

/-- `2^124 ≤ r0Tree x < 2^130` on the meaningful region. -/
theorem r0Tree_bounds {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    2 ^ 124 ≤ int256 (r0Tree x) ∧ int256 (r0Tree x) < 2 ^ 130 := by
  obtain ⟨_, hvlt⟩ := vTree_eq hx hC hC0
  obtain ⟨hev_lo, hev_hi⟩ := evTree_facts hvlt
  obtain ⟨htod_lo, htod_hi, _, _⟩ := todTree_bound hx hC hC0
  have hr0 : r0Tree x =
      evmDiv (evmMul scaleQ67 (evmAdd (evTree x) (todTree x))) (evmSub (evTree x) (todTree x)) := rfl
  rw [hr0]
  have hevw : evTree x < 2 ^ 256 := by unfold evTree; exact evmAdd_lt _ _
  have htodw : todTree x < 2 ^ 256 := by unfold todTree; exact evmSar_lt _ _
  refine r0Tree_bounds_ofEvTod hevw htodw ?_ ?_ ?_ ?_
  · have : (0x1385291795942d41ba5fd317688e18710 : Int) ≤ (evTree x : Int) := by exact_mod_cast hev_lo
    rw [show (0x1385291795942d41ba5fd317688e18710 : Int) = 415147853590918758559635130244235626256 by norm_num] at this
    exact this
  · have : (evTree x : Int) < ((3 * 2 ^ 127 : Nat) : Int) := by exact_mod_cast hev_hi
    rw [show ((3 * 2 ^ 127 : Nat) : Int) = 3 * 2 ^ 127 by norm_num] at this; exact this
  · rw [show (85070591730234615865843651857942052864 : Int) = 2 ^ 126 by norm_num]; exact htod_lo
  · rw [show (85070591730234615865843651857942052864 : Int) = 2 ^ 126 by norm_num]; exact htod_hi

end ExpYul

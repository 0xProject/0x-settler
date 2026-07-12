import ExpProof.Floor.PublicUncond
import LnProof.Theorems
import LnProof.Correct
import LnProof.Spec.Real

/-!
# The `lnWadToRay` round trip: `expRayToWad(lnWadToRay(w)) = w − 1`

`Exp.sol` documents the `Ln.lnWadToRay` composition on the central octave: for
`w` with `w/10¹⁸ ∈ [1/√2, √2)` the round trip returns `w − 1` (and `w` at the scale point
`w = 10¹⁸`). The proof targets that documented composition: `lnWadToRay`'s ≈10⁻⁹-ulp envelope keeps
the target `E` a fixed distance below the integer `w`, far above the ≈10⁻¹⁹-ulp accumulator deficit.

The proof composes the verified `lnWadToRay` runtime (`LnProof`) with the exp runtime:

* `lnWadToRayRuntimeCorrect` brackets `x = lnWadToRay(w)` against `X = 10²⁷·ln(w/10¹⁸)`
  (`x ≤ X < x + 2`), so `E = 10¹⁸·exp(x/10²⁷) = w·exp((x − X)/10²⁷) ∈ (w − 1, w]`;
* the exp runtime's strict never-over (`accumReal x < E`, from the `MARGIN` slack) and floor
  (`r1Tree x = ⌊accumReal x⌋`) pin `w − 1 ≤ accumReal x < w`, hence `r1Tree x = w − 1`;
* at `w = 10¹⁸`, `lnWadToRay(10¹⁸) = 0` and `expRayToWad(0) = 10¹⁸` (the scale-point pins).
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation
open Common.Word
open ExpRealSpec

noncomputable section

set_option maxRecDepth 100000

/-! ## Strict never-over: the accumulator stays a positive distance below the target

`accumReal_over` gives `accumReal x ≤ E`. The never-over envelope's image on the output grid is
below `0.934`, so `MARGIN = 1` exceeds it strictly. The round trip needs this
strictness to rule out `accumReal x = w` exactly. -/

/-- **Strict never-over.** On the region the real pre-floor accumulator is strictly below the
target. The proven over bound and its image below `MARGIN` give a strictly negative residue. -/
theorem accumReal_over_strict (x : Nat) (hx : x < 2 ^ 256) (hC : int256 Cmask < int256 x)
    (hC0 : int256 x < int256 C0thresh) :
    accumReal x < expRayToWadTarget (int256 x) := by
  obtain ⟨s, hsint, hAeq⟩ := accumReal_eq hx hC hC0
  have hps : (0 : Real) < (2 ^ s : Real) := by positivity
  have hfold := target_octave_fold s hsint
  have hover := r0_real_over_within hx hC hC0
  set Ert := Real.exp (reducedArg x) with hErt
  -- r0 − MARGIN < scaleQ67·Ert = E·2^s
  have hbound : (int256 (r0Tree x) : Real) - 1 <
      expRayToWadTarget (int256 x) * (2 ^ s : Real) := by
    rw [hfold]
    have hwad : (WAD : Real) = (10 ^ 18 : Real) := by unfold WAD; norm_num
    rw [hwad]
    have hBM := over_budget_image_lt_one
    linarith [hover, hBM]
  rw [hAeq, div_lt_iff₀ hps]; linarith [hbound]

/-- **Accumulator deficit, region-uniform.** On the region the accumulator is below the target by
strictly less than `39931/40000`: `E − 39931/40000 < accumReal x`. The deficit `r0 ≥ scaleQ67·exp(rt) − U`
(`U = 2993/1000`) and the octave fold give
`accumReal x ≥ E − (U + MARGIN)/2^s` with `s = 68 − k ≥ 4`, and `(U + MARGIN)/2² ≈ 0.998 < 39931/40000`.
The tightness below one is what closes the round trip together with `lnWadToRay`'s ≈10⁻⁹
envelope. -/
theorem accumReal_deficit_lt_one (x : Nat) (hx : x < 2 ^ 256) (hC : int256 Cmask < int256 x)
    (hC0 : int256 x < int256 C0thresh) :
    expRayToWadTarget (int256 x) - 39931 / 40000 < accumReal x := by
  obtain ⟨s, hsint, hAeq⟩ := accumReal_eq hx hC hC0
  have hps : (0 : Real) < (2 ^ s : Real) := by positivity
  have hfold := target_octave_fold s hsint
  have hunder := r0_real_under_within hx hC hC0
  obtain ⟨_, hkhi⟩ := kTree_bound hx hC hC0
  set Ert := Real.exp (reducedArg x) with hErt
  have hs4 : (2 : Int) ≤ (s : Int) := by rw [hsint]; linarith [hkhi]
  have hs4n : 2 ≤ s := by exact_mod_cast hs4
  have hpow : (2 ^ 2 : Real) ≤ (2 ^ s : Real) := pow_le_pow_right₀ (by norm_num) hs4n
  -- (E − 39931/40000)·2^s < r0 − MARGIN, since E·2^s = scaleQ67·Ert ≤ r0 + U
  -- and U + MARGIN < (39931/40000)·2⁴ ≤ (39931/40000)·2^s
  have hbound : (expRayToWadTarget (int256 x) - 39931 / 40000) * (2 ^ s : Real) <
      (int256 (r0Tree x) : Real) - 1 := by
    have hkey : expRayToWadTarget (int256 x) * (2 ^ s : Real) =
        (WAD : Real) * (2 ^ 67 : Real) * Ert := hfold
    have hwad : (WAD : Real) = (10 ^ 18 : Real) := by unfold WAD; norm_num
    rw [hwad] at hkey
    have hbudget : (2993 / 1000 : Real) + 1 < (39931 / 40000) * (2 ^ 2 : Real) := by norm_num
    have h2425 : (39931 / 40000 : Real) * (2 ^ 2 : Real) ≤ (39931 / 40000) * (2 ^ s : Real) :=
      mul_le_mul_of_nonneg_left hpow (by norm_num)
    nlinarith [hunder, hkey, hbudget, hpow, h2425]
  rw [hAeq, lt_div_iff₀ hps]; linarith [hbound]

/-! ## The `lnWadToRay` envelope on the round-trip band

`Wlo = ⌈10¹⁸/√2⌉` and `Whi = ⌊10¹⁸·√2⌋` are the integer endpoints of the half-open band
`w/10¹⁸ ∈ [1/√2, √2)`; over it `w/10¹⁸ ∈ (1/2, 2)`. -/

/-- The lower endpoint `⌈10¹⁸/√2⌉`. -/
def Wlo : Nat := 707106781186547525

/-- The upper endpoint `⌊10¹⁸·√2⌋`. -/
def Whi : Nat := 1414213562373095048

/-- `log 2 < 1` (from `2 < e`). -/
theorem log_two_lt_one : Real.log 2 < 1 := by
  have h2e : (2 : Real) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have := Real.log_lt_log (by norm_num : (0:Real) < 2) h2e
  rwa [Real.log_exp] at this

/-- The `Real`-valued ratio facts on the round-trip band: `1/2 < w/10¹⁸ < 2`. -/
theorem band_ratio_bounds {w : Nat} (hlo : Wlo ≤ w) (hhi : w ≤ Whi) :
    (1 : Real) / 2 < (w : Real) / (10 ^ 18 : Real) ∧
      (w : Real) / (10 ^ 18 : Real) < 2 := by
  have hwlo : (Wlo : Real) ≤ (w : Real) := by exact_mod_cast hlo
  have hwhi : (w : Real) ≤ (Whi : Real) := by exact_mod_cast hhi
  have hWlo : (Wlo : Real) = 707106781186547525 := by unfold Wlo; norm_num
  have hWhi : (Whi : Real) = 1414213562373095048 := by unfold Whi; norm_num
  rw [hWlo] at hwlo; rw [hWhi] at hwhi
  constructor
  · rw [lt_div_iff₀ (by positivity)]; linarith [hwlo]
  · rw [div_lt_iff₀ (by positivity)]; linarith [hwhi]

/-- **The `lnWadToRay` envelope.** For `w` on the round-trip band and the signed ray output `r` of
`lnWadToRay(w)` bracketed by `X = 10²⁷·ln(w/10¹⁸)` (`r ≤ X < r + 2`), the exp target
`E = expRayToWadTarget r` satisfies `w − 1 < E ≤ w`, and `r` lies in the exp region
`(Cmask, C0thresh)`. -/
theorem expTarget_band {w : Nat} (r : Int) (hlo : Wlo ≤ w) (hhi : w ≤ Whi)
    (hr_le : (r : Real) ≤ LnRealSpec.lnWadToRayTarget w)
    (hr_lt : LnRealSpec.lnWadToRayTarget w < ((r + 2 : Int) : Real)) :
    ((w : Real) - 69 / 40000 < expRayToWadTarget r ∧ expRayToWadTarget r ≤ (w : Real)) ∧
      int256 Cmask < r ∧ r < int256 C0thresh := by
  have hwpos : (0 : Real) < (w : Real) := by
    have : (0 : Nat) < w := lt_of_lt_of_le (by unfold Wlo; norm_num) hlo
    exact_mod_cast this
  obtain ⟨hratlo, hrathi⟩ := band_ratio_bounds hlo hhi
  -- abbreviations
  set L : Real := Real.log ((w : Real) / (10 ^ 18 : Real)) with hLdef
  have hXeq : LnRealSpec.lnWadToRayTarget w = (10 ^ 27 : Real) * L := by
    unfold LnRealSpec.lnWadToRayTarget LnRealSpec.wadRatio LnRealSpec.RAY LnRealSpec.WAD
    rw [hLdef]; push_cast; ring
  rw [hXeq] at hr_le hr_lt
  have hwr_pos : (0 : Real) < (w : Real) / (10 ^ 18 : Real) := by positivity
  have hexpL : Real.exp L = (w : Real) / (10 ^ 18 : Real) := by
    rw [hLdef, Real.exp_log hwr_pos]
  -- E = 10^18 · exp(r/10^27)
  have hEeq : expRayToWadTarget r = (10 ^ 18 : Real) * Real.exp ((r : Real) / (10 ^ 27 : Real)) := by
    unfold expRayToWadTarget WAD RAY; push_cast; ring
  -- never-over: r/10^27 ≤ L ⇒ exp ≤ w/10^18 ⇒ E ≤ w
  have hrle' : (r : Real) / (10 ^ 27 : Real) ≤ L := by
    rw [div_le_iff₀ (by positivity)]; nlinarith [hr_le]
  have hEle : expRayToWadTarget r ≤ (w : Real) := by
    rw [hEeq]
    have hexp_le : Real.exp ((r : Real) / (10 ^ 27 : Real)) ≤ Real.exp L := Real.exp_le_exp.mpr hrle'
    rw [hexpL] at hexp_le
    have : (10 ^ 18 : Real) * Real.exp ((r : Real) / (10 ^ 27 : Real)) ≤
        (10 ^ 18 : Real) * ((w : Real) / (10 ^ 18 : Real)) :=
      mul_le_mul_of_nonneg_left hexp_le (by norm_num)
    calc (10 ^ 18 : Real) * Real.exp ((r : Real) / (10 ^ 27 : Real)) ≤
          (10 ^ 18 : Real) * ((w : Real) / (10 ^ 18 : Real)) := this
      _ = (w : Real) := by field_simp
  -- deficit: r/10^27 > L − 2/10^27 ⇒ exp > (w/10^18)·exp(−2/10^27) ≥ (w/10^18)·(1 − 2/10^27)
  have hrgt' : L - 2 / (10 ^ 27 : Real) < (r : Real) / (10 ^ 27 : Real) := by
    rw [lt_div_iff₀ (by positivity)]; push_cast at hr_lt; nlinarith [hr_lt]
  have hElt : (w : Real) - 69 / 40000 < expRayToWadTarget r := by
    rw [hEeq]
    -- exp(r/10^27) > exp(L − 2/10^27) = exp(L)·exp(−2/10^27)
    have hexp_gt : Real.exp (L - 2 / (10 ^ 27 : Real)) < Real.exp ((r : Real) / (10 ^ 27 : Real)) :=
      Real.exp_lt_exp.mpr hrgt'
    have hsplit : Real.exp (L - 2 / (10 ^ 27 : Real)) =
        ((w : Real) / (10 ^ 18 : Real)) * Real.exp (-(2 / (10 ^ 27 : Real))) := by
      rw [show L - 2 / (10 ^ 27 : Real) = L + (-(2 / (10 ^ 27 : Real))) from by ring,
        Real.exp_add, hexpL]
    -- exp(−u) ≥ 1 − u
    have hone : (1 : Real) + (-(2 / (10 ^ 27 : Real))) ≤ Real.exp (-(2 / (10 ^ 27 : Real))) := by
      have := Real.add_one_le_exp (-(2 / (10 ^ 27 : Real))); linarith [this]
    have hwr_nn : (0 : Real) ≤ (w : Real) / (10 ^ 18 : Real) := le_of_lt hwr_pos
    -- (w/10^18)·exp(−u) ≥ (w/10^18)·(1 − u)
    have hstep : ((w : Real) / (10 ^ 18 : Real)) * (1 - 2 / (10 ^ 27 : Real)) ≤
        ((w : Real) / (10 ^ 18 : Real)) * Real.exp (-(2 / (10 ^ 27 : Real))) :=
      mul_le_mul_of_nonneg_left (by linarith [hone]) hwr_nn
    -- 10^18 · (w/10^18)·(1 − 2/10^27) = w − 2w/10^27 > w − 69/40000 since 2w·40000 < 69·10^27
    have h2w : 40000 * (2 * (w : Real)) < 69 * (10 ^ 27 : Real) := by
      have : (w : Real) ≤ (Whi : Real) := by exact_mod_cast hhi
      have hWhi : (Whi : Real) = 1414213562373095048 := by unfold Whi; norm_num
      rw [hWhi] at this; linarith [this]
    have hexp_r_gt : ((w : Real) / (10 ^ 18 : Real)) * (1 - 2 / (10 ^ 27 : Real)) <
        Real.exp ((r : Real) / (10 ^ 27 : Real)) := by
      rw [hsplit] at hexp_gt; linarith [hstep, hexp_gt]
    have hmul : (10 ^ 18 : Real) * (((w : Real) / (10 ^ 18 : Real)) * (1 - 2 / (10 ^ 27 : Real))) <
        (10 ^ 18 : Real) * Real.exp ((r : Real) / (10 ^ 27 : Real)) :=
      mul_lt_mul_of_pos_left hexp_r_gt (by norm_num)
    have hlhs : (10 ^ 18 : Real) * (((w : Real) / (10 ^ 18 : Real)) * (1 - 2 / (10 ^ 27 : Real))) =
        (w : Real) - 2 * (w : Real) / (10 ^ 27 : Real) := by field_simp; ring
    rw [hlhs] at hmul
    -- w − 2w/10^27 > w − 69/40000 since 2w/10^27 < 69/40000
    have h2wd : 2 * (w : Real) / (10 ^ 27 : Real) < 69 / 40000 := by
      rw [div_lt_iff₀ (by positivity)]; linarith [h2w]
    linarith [hmul, h2wd]
  -- region membership of r
  have hCmask : int256 Cmask = -41446531673892822312323846185 := int256_Cmask
  have hC0 : int256 C0thresh = 45401140326676417766828703956 := int256_C0thresh
  -- L > log(1/2) = −log 2 > −1 ; X = 10^27·L > −10^27 ; r ≥ X − 2 > Cmask
  have hLgt : -(1 : Real) < L := by
    have h12 : Real.log ((1:Real)/2) < L := by
      rw [hLdef]; exact Real.log_lt_log (by norm_num) hratlo
    have hlog12 : Real.log ((1:Real)/2) = -(Real.log 2) := by
      rw [show (1:Real)/2 = (2:Real)⁻¹ from by norm_num, Real.log_inv]
    rw [hlog12] at h12
    linarith [h12, log_two_lt_one]
  have hLlt : L < 1 := by
    have h2 : L < Real.log 2 := by rw [hLdef]; exact Real.log_lt_log hwr_pos hrathi
    linarith [h2, log_two_lt_one]
  refine ⟨⟨hElt, hEle⟩, ?_, ?_⟩
  · -- Cmask < r : r > 10^27·L − 2 > −10^27 − 2 > Cmask
    rw [hCmask]
    have hXlo : -(10 ^ 27 : Real) < (10 ^ 27 : Real) * L := by nlinarith [hLgt]
    have hr_gt_X2 : (10 ^ 27 : Real) * L - 2 < (r : Real) := by push_cast at hr_lt; linarith [hr_lt]
    have : (-41446531673892822312323846185 : Real) < (r : Real) := by
      have : (-41446531673892822312323846185 : Real) < -(10 ^ 27 : Real) - 2 := by norm_num
      linarith [this, hXlo, hr_gt_X2]
    exact_mod_cast this
  · -- r < C0thresh : r ≤ 10^27·L < 10^27 < C0thresh
    rw [hC0]
    have hXhi : (10 ^ 27 : Real) * L < (10 ^ 27 : Real) := by nlinarith [hLlt]
    have : (r : Real) < (45401140326676417766828703956 : Real) := by
      have hc : (10 ^ 27 : Real) < (45401140326676417766828703956 : Real) := by norm_num
      linarith [hr_le, hXhi, hc]
    exact_mod_cast this

/-! ## Floor pinning: the body returns exactly `w − 1`

With strict never-over (`accumReal x < E ≤ w`) and the region-uniform deficit
(`accumReal x > E − 39931/40000 > w − 1`), the accumulator lies in `(w − 1, w)`, so its floor — the body
word `r1Tree x` — is exactly `w − 1`. -/

/-- **Floor pin.** On the region, if `w − 69/40000 < E ≤ w` then the floored body word is exactly
`w − 1`. The strict never-over puts `accumReal x < E ≤ w`, and the region-uniform deficit puts
`accumReal x > E − 39931/40000 > w − 1`, so `accumReal x ∈ (w − 1, w)` and its floor is `w − 1`. -/
theorem r1Tree_eq_w_sub_one {x w : Nat} (hx : x < 2 ^ 256) (hC : int256 Cmask < int256 x)
    (hC0 : int256 x < int256 C0thresh)
    (hElt : (w : Real) - 69 / 40000 < expRayToWadTarget (int256 x))
    (hEle : expRayToWadTarget (int256 x) ≤ (w : Real)) :
    int256 (r1Tree x) = (w : Int) - 1 := by
  set R1 : Int := int256 (r1Tree x) with hR1def
  obtain ⟨hfl, hfl1⟩ := r1Tree_floor_accum hx hC hC0
  have hover := accumReal_over_strict x hx hC hC0
  have hdef := accumReal_deficit_lt_one x hx hC hC0
  -- upper: R1 ≤ accum < E ≤ w  ⇒  R1 < w  ⇒  R1 ≤ w − 1
  have hRltw : (R1 : Real) < (w : Real) :=
    calc (R1 : Real) ≤ accumReal x := hfl
      _ < expRayToWadTarget (int256 x) := hover
      _ ≤ (w : Real) := hEle
  have hRle : R1 ≤ (w : Int) - 1 := by
    have : R1 < (w : Int) := by exact_mod_cast hRltw
    omega
  -- lower: accum > E − 39931/40000 > (w − 69/40000) − 39931/40000 = w − 1 ; accum < R1 + 1 ⇒ R1 + 1 > w − 1
  have hacc_lo : (w : Real) - 1 < accumReal x := by linarith [hdef, hElt]
  have hR1_gt : (w : Real) - 2 < (R1 : Real) := by linarith [hacc_lo, hfl1]
  have hRge : (w : Int) - 1 ≤ R1 := by
    have : (w : Int) - 1 < R1 + 1 := by
      exact_mod_cast (by linarith [hR1_gt] : (w : Real) - 1 < (R1 : Real) + 1)
    omega
  omega

/-! ## The round trip

`run_exp_ray_to_wad_evm (run_ln_wad_to_ray_evm w) = w − 1` for `w` on the band, `= w` at the scale
point. The composition feeds the verified `lnWadToRay` Nat output straight into the exp runtime.

The runtime bodies (`lnWadToRayBody`, `expTree`, `r1Tree`) are deep arithmetic trees; their
definitions are kept opaque here so that floor/cast reasoning over the composed result never forces
the kernel to whnf-reduce them (which overflows the recursion stack). -/

attribute [local irreducible] LnYul.lnWadToRayBody expTree r1Tree r0Tree kTree

/-- The Nat ln output and its facts: for `w` on the band the `lnWadToRay` runtime succeeds with a
256-bit word `result` whose signed value `int256 result` is bracketed against `10²⁷·ln(w/10¹⁸)`. -/
theorem lnWadToRay_band_run {w : Nat} (hlo : Wlo ≤ w) (hhi : w ≤ Whi) :
    ∃ result : Nat, LnYul.run_ln_wad_to_ray_evm w = .ok result ∧ result < 2 ^ 256 ∧
      (int256 result : Real) ≤ LnRealSpec.lnWadToRayTarget w ∧
      LnRealSpec.lnWadToRayTarget w < ((int256 result + 2 : Int) : Real) := by
  have hwlt : w < 2 ^ 256 := by
    have : w ≤ Whi := hhi
    have hWhi : Whi < 2 ^ 256 := by unfold Whi; norm_num
    omega
  have hux : u256 w = w := u256_of_lt hwlt
  have hwpos_nat : 0 < w := lt_of_lt_of_le (by unfold Wlo; norm_num) hlo
  have hpos : 1 ≤ u256 w := by rw [hux]; omega
  have hpos2 : u256 w < 2 ^ 255 := by
    rw [hux]; have hWhi : Whi < 2 ^ 255 := by unfold Whi; norm_num
    omega
  -- the runtime body
  have hrun := LnYul.run_ln_wad_to_ray_evm_eq_body w hpos hpos2
  rw [hux] at hrun
  set result : Nat := LnYul.lnWadToRayBody w with hresdef
  have hreslt : result < 2 ^ 256 := LnYul.lnWadToRayBody_lt hwlt
  -- the spec bracket, via the public correctness theorem
  have hsigned : LnYul.signedPositiveInput w := by
    unfold LnYul.signedPositiveInput; rw [hux, int256_of_lt (by omega : w < 2 ^ 255)]
    exact_mod_cast hwpos_nat
  obtain ⟨r, hrunsigned, hspec⟩ := LnYul.lnWadToRayRuntimeCorrect w hwlt hsigned
  -- identify r with int256 result
  rw [LnYul.runLnWadToRaySigned_ok_iff] at hrunsigned
  obtain ⟨result', hrun', hsr⟩ := hrunsigned
  rw [hrun] at hrun'
  have hres' : result' = result := Except.ok.inj hrun'.symm
  subst hres'
  have hreq : r = int256 result := by
    rw [← hsr]; show int256 (u256 result) = int256 result
    rw [u256_of_lt hreslt]
  subst hreq
  obtain ⟨hle, hlt⟩ := hspec
  exact ⟨result, hrun, hreslt, hle, hlt⟩

/-- **The `lnWadToRay` round trip.** For every `w` whose ratio lies in the
central band `w/10¹⁸ ∈ [1/√2, √2)` — equivalently `Wlo ≤ w ≤ Whi` — the composition
`expRayToWad ∘ lnWadToRay` recovers `w − 1`, and recovers `w` exactly at the scale point
`w = 10¹⁸`. Stated at the runtime level: `lnWadToRay`'s 256-bit output `x` fed straight into the exp
runtime returns the documented value. -/
theorem run_exp_ray_to_wad_evm_lnWadToRay_roundTrip {w : Nat} (hlo : Wlo ≤ w) (hhi : w ≤ Whi) :
    ∃ x r : Nat, LnYul.run_ln_wad_to_ray_evm w = .ok x ∧ run_exp_ray_to_wad_evm x = .ok r ∧
      (w = 10 ^ 18 → (r : Int) = 10 ^ 18) ∧ (w ≠ 10 ^ 18 → (r : Int) = (w : Int) - 1) := by
  obtain ⟨x, hlnrun, hxlt, hle, hlt⟩ := lnWadToRay_band_run hlo hhi
  -- the exp target bracket + region membership for x's signed value
  obtain ⟨⟨hElt, hEle⟩, hCmask, hC0⟩ := expTarget_band (int256 x) hlo hhi hle hlt
  refine ⟨x, expTree x, hlnrun, run_exp_ray_to_wad_evm_eq_expTree x (domain_of_below_C0 hxlt hC0),
    ?_, ?_⟩
  · -- scale point: w = 10^18 ⇒ x = 0 ⇒ expTree 0 = 10^18
    intro hw
    subst hw
    -- lnWadToRay(10^18) = 0
    have hx0 : x = 0 := by
      have := LnYul.run_ln_wad_to_ray_evm_zero_at_wad
      rw [this] at hlnrun; exact (Except.ok.inj hlnrun).symm
    subst hx0
    have he : expTree 0 = 1000000000000000000 := by
      have := run_exp_ray_to_wad_evm_zero
      rw [run_exp_ray_to_wad_evm_eq_expTree 0 (domain_of_below_C0 hxlt hC0)] at this
      exact Except.ok.inj this
    rw [he]; norm_num
  · -- non scale point: x ≠ 0, region ⇒ body word = w − 1
    intro hw
    have hx_ne : x ≠ 0 := by
      intro hx0
      -- x = 0 ⇒ int256 x = 0 ⇒ E = 10^18 ; but E ≤ w and w − 69/40000 < E so w ∈ (E, E + 69/40000]; w = 10^18
      apply hw
      have hE0 : expRayToWadTarget (int256 x) = (10 ^ 18 : Real) := by
        rw [hx0]; show expRayToWadTarget (int256 (0 : Nat)) = (10 ^ 18 : Real)
        have : int256 (0 : Nat) = (0 : Int) := rfl
        rw [this, expRayToWadTarget_zero]; unfold WAD; norm_num
      -- 10^18 ≤ w and w − 69/40000 < 10^18  ⇒  w = 10^18 (integers)
      rw [hE0] at hElt hEle
      have hwge : (10 ^ 18 : Real) ≤ (w : Real) := hEle
      have hwlt : (w : Real) < (10 ^ 18 : Real) + 69 / 40000 := by linarith [hElt]
      have h1 : (10 : Int) ^ 18 ≤ (w : Int) := by exact_mod_cast hwge
      have h2 : (w : Real) < (10 ^ 18 : Real) + 1 := by linarith [hwlt]
      have h3 : (w : Int) < (10 : Int) ^ 18 + 1 := by exact_mod_cast h2
      omega
    have hC : int256 Cmask < int256 x := hCmask
    -- the floored body word equals w − 1
    have hbody : int256 (r1Tree x) = (w : Int) - 1 := r1Tree_eq_w_sub_one hxlt hC hC0 hElt hEle
    -- expTree x = r1Tree x on the region (x ≠ 0)
    have hexpeq : int256 (expTree x) = int256 (r1Tree x) :=
      int256_expTree_region_ne_zero hxlt hC hC0 hx_ne
    -- the body word is nonnegative (= w − 1 ≥ 0), so int256 (expTree x) = (expTree x : Int)
    have hge1 : 1 ≤ w := le_trans (by unfold Wlo; norm_num) hlo
    have hbody_pos : (0 : Int) ≤ (w : Int) - 1 := by
      have : (1 : Int) ≤ (w : Int) := by exact_mod_cast hge1
      omega
    have hexp_nn : 0 ≤ int256 (expTree x) := by rw [hexpeq, hbody]; exact hbody_pos
    have hexp_word : int256 (expTree x) = (expTree x : Int) :=
      (int256_eq_of_nonneg (expTree_lt x) hexp_nn).1
    rw [← hexp_word, hexpeq, hbody]

/-- info: 'ExpYul.run_exp_ray_to_wad_evm_lnWadToRay_roundTrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_exp_ray_to_wad_evm_lnWadToRay_roundTrip

/-- The `lnWadToRay` round trip as a single canonical result expression. -/
theorem run_exp_ray_to_wad_evm_lnWadToRay_roundTrip_if {w : Nat} (hlo : Wlo ≤ w) (hhi : w ≤ Whi) :
    ∃ x r : Nat, LnYul.run_ln_wad_to_ray_evm w = .ok x ∧ run_exp_ray_to_wad_evm x = .ok r ∧
      (r : Int) = if w = 10 ^ 18 then (w : Int) else (w : Int) - 1 := by
  obtain ⟨x, r, hln, hexp, hscale, hne⟩ := run_exp_ray_to_wad_evm_lnWadToRay_roundTrip hlo hhi
  refine ⟨x, r, hln, hexp, ?_⟩
  by_cases hw : w = 10 ^ 18
  · rw [if_pos hw]
    rw [hw]
    exact hscale hw
  · rw [if_neg hw]
    exact hne hw

/-- info: 'ExpYul.run_exp_ray_to_wad_evm_lnWadToRay_roundTrip_if' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_exp_ray_to_wad_evm_lnWadToRay_roundTrip_if

end

end ExpYul

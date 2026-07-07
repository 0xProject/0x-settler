import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Common.Seam.RealExpBridge
import LnProof.Spec.Real
import LnProof.Spec.Cut

open scoped BigOperators

namespace LnRealBridge

open Common.Exp Common.RealExpBridge LnFloor LnFloorCert

noncomputable section

lemma QS_pos : 0 < QS := LnFloor.QS_pos

lemma ray_exp_arg_of_nonneg {r : Int} (hr : 0 ≤ r) :
    (((r.toNat * 2 ^ 99 : Nat) : Real) / ((QS : Nat) : Real)) =
      (r : Real) / ((10 ^ 27 : Nat) : Real) := by
  have hrnat : ((r.toNat : Nat) : Real) = (r : Real) := by
    exact_mod_cast Int.toNat_of_nonneg hr
  unfold QS
  norm_num [Nat.cast_mul, Nat.cast_pow, hrnat]
  field_simp
  ring

lemma ray_exp_arg_of_neg {r : Int} (hr : r < 0) :
    ((((-r).toNat * 2 ^ 99 : Nat) : Real) / ((QS : Nat) : Real)) =
      -((r : Real) / ((10 ^ 27 : Nat) : Real)) := by
  rw [ray_exp_arg_of_nonneg (r := -r) (by omega)]
  norm_num [Int.cast_neg]
  ring

lemma ray_exp_arg_of_nonpos {r : Int} (hr : r ≤ 0) :
    ((((-r).toNat * 2 ^ 99 : Nat) : Real) / ((QS : Nat) : Real)) =
      -((r : Real) / ((10 ^ 27 : Nat) : Real)) := by
  rw [ray_exp_arg_of_nonneg (r := -r) (by omega)]
  norm_num [Int.cast_neg]
  ring

lemma wadRatio_pos {x : Nat} (hx : 0 < x) : 0 < (x : Real) / ((10 ^ 18 : Nat) : Real) := by
  have hxR : 0 < (x : Real) := by exact_mod_cast hx
  exact div_pos hxR (by norm_num)

lemma wadReciprocal_pos {x : Nat} (hx : 0 < x) : 0 < ((10 ^ 18 : Nat) : Real) / x := by
  have hxR : 0 < (x : Real) := by exact_mod_cast hx
  exact div_pos (by norm_num) hxR

lemma reciprocal_wadRatio {x : Nat} (hx : 0 < x) :
    ((10 ^ 18 : Nat) : Real) / x = ((x : Real) / ((10 ^ 18 : Nat) : Real))⁻¹ := by
  have hxR : (x : Real) ≠ 0 := by exact_mod_cast ne_of_gt hx
  field_simp [hxR]

lemma le_rayLog_of_cutLeLogWadRay {r : Int} {x : Nat} (hx : 0 < x)
    (hcut : CutLeLogWadRay r x) :
    (r : Real) ≤ ((10 ^ 27 : Nat) : Real) * Real.log ((x : Real) / ((10 ^ 18 : Nat) : Real)) := by
  have hRpos : 0 < ((10 ^ 27 : Nat) : Real) := by norm_num
  have hratio : 0 < (x : Real) / ((10 ^ 18 : Nat) : Real) := wadRatio_pos hx
  by_cases hr : 0 ≤ r
  · have hc : capUB (r.toNat * 2 ^ 99) QS x (10 ^ 18) := by
      simpa [CutLeLogWadRay, CutExpLe, hr] using hcut
    have he := exp_le_of_capUB QS_pos (by decide : 0 < (10 ^ 18 : Nat)) hc
    rw [ray_exp_arg_of_nonneg hr] at he
    have hlog : (r : Real) / ((10 ^ 27 : Nat) : Real) ≤
        Real.log ((x : Real) / ((10 ^ 18 : Nat) : Real)) :=
      (Real.le_log_iff_exp_le hratio).mpr he
    have hmul := (div_le_iff₀ hRpos).mp hlog
    nlinarith
  · have hrlt : r < 0 := by omega
    have hc : capLB ((-r).toNat * 2 ^ 99) QS (10 ^ 18) x := by
      simpa [CutLeLogWadRay, CutRatioLeExp, hr] using hcut
    have he := le_exp_of_capLB QS_pos hx hc
    rw [ray_exp_arg_of_neg hrlt] at he
    have hrecpos : 0 < ((10 ^ 18 : Nat) : Real) / x := wadReciprocal_pos hx
    have hlogrec : Real.log (((10 ^ 18 : Nat) : Real) / x) ≤
        -((r : Real) / ((10 ^ 27 : Nat) : Real)) :=
      (Real.log_le_iff_le_exp hrecpos).mpr he
    rw [reciprocal_wadRatio hx, Real.log_inv] at hlogrec
    have hlog : (r : Real) / ((10 ^ 27 : Nat) : Real) ≤
        Real.log ((x : Real) / ((10 ^ 18 : Nat) : Real)) := by
      nlinarith
    have hmul := (div_le_iff₀ hRpos).mp hlog
    nlinarith

lemma wadRatio_lt_upperMargin {x : Nat} (hx : 0 < x) :
    (x : Real) / ((10 ^ 18 : Nat) : Real) <
      ((x * 10 ^ 31 : Nat) : Real) /
        (((10 ^ 18) * (10 ^ 31 - 10) : Nat) : Real) := by
  have hxR : 0 < (x : Real) := by exact_mod_cast hx
  norm_num [Nat.cast_mul, Nat.cast_pow]
  nlinarith [hxR]

lemma lowerMargin_lt_wadReciprocal {x : Nat} (hx : 0 < x) :
    (((10 ^ 18) * (10 ^ 31 - 10) : Nat) : Real) / ((x * 10 ^ 31 : Nat) : Real) <
      ((10 ^ 18 : Nat) : Real) / x := by
  have hxR : 0 < (x : Real) := by exact_mod_cast hx
  norm_num [Nat.cast_mul, Nat.cast_pow]
  have hden : 0 < (x : Real) * 10000000000000000000000000000000 := by positivity
  rw [div_lt_iff₀ hden]
  have hcancel : 1000000000000000000 / (x : Real) *
      ((x : Real) * 10000000000000000000000000000000) =
      1000000000000000000 * 10000000000000000000000000000000 := by
    field_simp [hxR.ne']
    ring
  rw [hcancel]
  norm_num

lemma rayLog_lt_of_cutLogWadRayLtWithMargin {b : Int} {x : Nat} (hx : 0 < x)
    (hcut : CutLogWadRayLtWithMargin x b) :
    ((10 ^ 27 : Nat) : Real) * Real.log ((x : Real) / ((10 ^ 18 : Nat) : Real)) < (b : Real) := by
  have hRpos : 0 < ((10 ^ 27 : Nat) : Real) := by norm_num
  have hratio : 0 < (x : Real) / ((10 ^ 18 : Nat) : Real) := wadRatio_pos hx
  by_cases hb : 1 ≤ b
  · have hb0 : 0 ≤ b := by omega
    have hc : capLB (b.toNat * 2 ^ 99) QS (x * 10 ^ 31) (10 ^ 18 * (10 ^ 31 - 10)) := by
      simpa [CutLogWadRayLtWithMargin, CutRatioLeExp, hb] using hcut
    have he := le_exp_of_capLB QS_pos (by decide : 0 < (10 ^ 18 * (10 ^ 31 - 10) : Nat)) hc
    rw [ray_exp_arg_of_nonneg hb0] at he
    have hmargin := wadRatio_lt_upperMargin hx
    have hlt_exp : (x : Real) / ((10 ^ 18 : Nat) : Real) <
        Real.exp ((b : Real) / ((10 ^ 27 : Nat) : Real)) := lt_of_lt_of_le hmargin he
    have hlog : Real.log ((x : Real) / ((10 ^ 18 : Nat) : Real)) <
        (b : Real) / ((10 ^ 27 : Nat) : Real) :=
      (Real.log_lt_iff_lt_exp hratio).mpr hlt_exp
    have hmul := (lt_div_iff₀' hRpos).mp hlog
    nlinarith
  · have hb0 : b ≤ 0 := by omega
    have hc : capUB ((-b).toNat * 2 ^ 99) QS (10 ^ 18 * (10 ^ 31 - 10)) (x * 10 ^ 31) := by
      simpa [CutLogWadRayLtWithMargin, CutExpLe, hb] using hcut
    have he := exp_le_of_capUB QS_pos (by exact Nat.mul_pos hx (by decide : 0 < (10 ^ 31 : Nat))) hc
    rw [ray_exp_arg_of_nonpos hb0] at he
    have hmargin := lowerMargin_lt_wadReciprocal hx
    have hlt_rec : Real.exp (-((b : Real) / ((10 ^ 27 : Nat) : Real))) <
        ((10 ^ 18 : Nat) : Real) / x := lt_of_le_of_lt he hmargin
    have hrecpos : 0 < ((10 ^ 18 : Nat) : Real) / x := wadReciprocal_pos hx
    have hlogrec : -((b : Real) / ((10 ^ 27 : Nat) : Real)) <
        Real.log (((10 ^ 18 : Nat) : Real) / x) :=
      (Real.lt_log_iff_exp_lt hrecpos).mpr hlt_rec
    rw [reciprocal_wadRatio hx, Real.log_inv] at hlogrec
    have hlog : Real.log ((x : Real) / ((10 ^ 18 : Nat) : Real)) <
        (b : Real) / ((10 ^ 27 : Nat) : Real) := by
      nlinarith
    have hmul := (lt_div_iff₀' hRpos).mp hlog
    nlinarith

lemma cutLnWadRayBracket_real {r : Int} {x : Nat} (hx : 0 < x)
    (hcut : CutLnWadRayBracket r x) : LnRealSpec.LnWadToRaySpec x r := by
  unfold LnRealSpec.LnWadToRaySpec LnRealSpec.lnWadToRayTarget LnRealSpec.wadRatio
  constructor
  · simpa [LnRealSpec.RAY, LnRealSpec.WAD] using le_rayLog_of_cutLeLogWadRay (r := r) (x := x) hx hcut.1
  · simpa [LnRealSpec.RAY, LnRealSpec.WAD, Int.cast_add, Int.cast_ofNat] using
      rayLog_lt_of_cutLogWadRayLtWithMargin (b := r + 2) (x := x) hx hcut.2

lemma cutLnWadSpec_real {ray wad : Int} {x : Nat} (hx : 0 < x)
    (hcut : CutLnWadSpec ray wad x) : LnRealSpec.LnWadSpec x wad := by
  obtain ⟨hrayCut, hfloorlo, hfloorhi⟩ := hcut
  have hray := cutLnWadRayBracket_real (r := ray) (x := x) hx hrayCut
  unfold LnRealSpec.LnWadToRaySpec LnRealSpec.lnWadToRayTarget LnRealSpec.wadRatio at hray
  unfold LnRealSpec.LnWadSpec LnRealSpec.lnWadTarget LnRealSpec.wadRatio
  simp [LnRealSpec.RAY, LnRealSpec.WAD] at hray ⊢
  have hfloorloR : (wad : Real) * (1000000000 : Real) ≤ (ray : Real) := by
    exact_mod_cast hfloorlo
  have hfloorhiR : (ray : Real) < ((wad + 1 : Int) : Real) * (1000000000 : Real) := by
    exact_mod_cast hfloorhi
  constructor
  · have hscale : ((10 ^ 27 : Nat) : Real) = (1000000000 : Real) * ((10 ^ 18 : Nat) : Real) := by
      norm_num
    nlinarith [hray.1, hfloorloR, hscale]
  · have hscale : ((10 ^ 27 : Nat) : Real) = (1000000000 : Real) * ((10 ^ 18 : Nat) : Real) := by
      norm_num
    have hwide : ((wad + 1 : Int) : Real) * (1000000000 : Real) + 2 ≤
        ((wad + 2 : Int) : Real) * (1000000000 : Real) := by
      norm_num [Int.cast_add]
      ring_nf
      linarith
    norm_num [Int.cast_add] at hfloorhiR hwide
    nlinarith [hray.2, hfloorhiR, hwide, hscale]

end

end LnRealBridge

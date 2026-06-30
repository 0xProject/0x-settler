import ExpProof.Floor.R0Exp

/-!
# The deficit (under) side of the per-point `r0`-vs-`exp` bridge

This module contains the counterpart to the never-over `r0_real_over_within`: the per-point deficit
`2¹²⁶·exp(rt) ≤ r0 + 8` (`r0_real_under_within`), both signs.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation
open Common.Poly

set_option maxRecDepth 100000
set_option maxHeartbeats 1600000

/-! ## The deficit (under) side: per-point `2¹²⁶·exp(rt) ≤ r0 + 8` (both signs)

Mirror of the never-over `r0_real_over_within`. The nonneg half drops the even truncation
`Ee·(2¹²⁶−r0) ≤ 0` and bounds the tod truncation; the negative half drops the tod and bounds the
even truncation. Both feed the closing-shift deficit budget `c_under < 8.43 = 2⁶³/WAD − MARGIN/WAD`
at the binding `k = 63`. -/

/-- **`todNumV` upper bound (nonneg half).** For `0 ≤ t`:
`todNumV(t) ≤ 2¹¹⁹³·tod + 2¹¹⁹³ + W_od·2¹⁰³⁹·t`. -/
theorem todNumV_ub {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htnn : 0 ≤ int256 (tTree x)) :
    evalPoly ExpCertV.todNumV (int256 (tTree x)) ≤
      2 ^ 1193 * (int256 (todTree x)) + 2 ^ 1193 + 69402657 * 2 ^ 1039 * (int256 (tTree x)) := by
  obtain ⟨_, _, _, htodhi⟩ := todTree_bound hx hC hC0
  obtain ⟨_, hodhi⟩ := odNumVPoly_bracket hx hC hC0
  set t := int256 (tTree x) with htdef
  rw [evalTodNumV]
  -- todP = 2^23·t·odpoly.  t ≥ 0, odpoly ≤ 2^1042·od + W_od·2^1016 ⟹ 2^23·t·odpoly ≤ 2^23·t·(…)
  have hmul : 2 ^ 23 * (t * evalPoly ExpCertV.odNumVPoly t) ≤
      2 ^ 23 * (t * (2 ^ 1042 * (odTree x : Int) + 69402657 * 2 ^ 1016)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_left (le_of_lt hodhi) htnn
  -- 2^23·t·(2^1042 od + W_od 2^1016) = 2^1065·(t·od) + W_od·2^1039·t ;  2^1065·(t·od) < 2^1193·tod + 2^1193
  have htod_hi : t * (odTree x : Int) < (2 ^ 128 : Int) * (int256 (todTree x)) + 2 ^ 128 := htodhi
  have key : 2 ^ 23 * (t * (2 ^ 1042 * (odTree x : Int) + 69402657 * 2 ^ 1016)) ≤
      2 ^ 1193 * (int256 (todTree x)) + 2 ^ 1193 + 69402657 * 2 ^ 1039 * t := by
    have e1 : 2 ^ 23 * (t * (2 ^ 1042 * (odTree x : Int) + 69402657 * 2 ^ 1016)) =
        2 ^ 1065 * (t * (odTree x : Int)) + 69402657 * 2 ^ 1039 * t := by ring
    have e2 : (2 : Int) ^ 1065 * ((2 ^ 128 : Int) * (int256 (todTree x)) + 2 ^ 128) =
        2 ^ 1193 * (int256 (todTree x)) + 2 ^ 1193 := by
      rw [show (2:Int) ^ 1193 = 2 ^ 1065 * 2 ^ 128 from by rw [← pow_add]]; ring
    rw [e1]
    have h := mul_le_mul_of_nonneg_left (le_of_lt htod_hi) (by positivity : (0:Int) ≤ 2 ^ 1065)
    rw [e2] at h
    linarith [h]
  linarith [hmul, key]

/-- **`num ≤ 1.45·den`** (`ê ≤ 1.45`) on the nonneg half, from `exp(t/2¹²⁸) ≤ √2` and the cert. -/
theorem num_le_145_den {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htnn : 0 ≤ int256 (tTree x)) :
    100 * ((evTree x : Int) + int256 (todTree x)) ≤ 145 * ((evTree x : Int) - int256 (todTree x)) := by
  obtain ⟨_, hthi⟩ := tTree_in_cert_domain hx hC hC0
  set t := int256 (tTree x) with htdef
  have htdom : t ≤ (ExpCertV.H128 : Int) := by
    rw [show ((ExpCertV.H128 : Nat) : Int) = 117932881612756647068972071382077242199 from by
      unfold ExpCertV.H128; norm_num]
    exact hthi
  have hDElb := denExpV_lb hx hC hC0 htnn
  set NE := evalPoly ExpCertV.numExpV t with hNEdef
  set DE := evalPoly ExpCertV.denExpV t with hDEdef
  have hDEpos_int : (0 : Int) < DE := by
    have : (0:Int) < 2 ^ 1317 := by positivity
    linarith [hDElb, this]
  have hDEpos : (0 : Real) < (DE : Real) := by exact_mod_cast hDEpos_int
  set Et := Real.exp ((t : Real) / (2 ^ 128 : Real)) with hEtdef
  have hcertlo := certLo_real htnn htdom
  set Mp : Real := (2 ^ 130 : Real) / ((2 ^ 130 : Real) - 1) with hMpdef
  have hEtsqrt2 := exp_t_le_sqrt2 hx hC hC0 htnn
  rw [← hEtdef] at hEtsqrt2
  have hMp_pos : (0:Real) < Mp := by rw [hMpdef]; positivity
  have hNEDE_le : (NE : Real) / (DE : Real) ≤ Et * Mp := by
    have hc : ((2 ^ 130 - 1 : Int) : Real) * (NE : Real) /
        (((2 ^ 130 : Int) : Real) * (DE : Real)) ≤ Et := hcertlo
    rw [hMpdef]
    have key : (NE : Real) / (DE : Real) =
        ((2 ^ 130 : Real) / ((2 ^ 130 : Real) - 1)) *
          (((2 ^ 130 - 1 : Int) : Real) * (NE : Real) /
            (((2 ^ 130 : Int) : Real) * (DE : Real))) := by
      push_cast; field_simp; ring
    rw [key, mul_comm Et _]; exact mul_le_mul_of_nonneg_left hc (by positivity)
  -- num bound: 2^1193·num ≤ NE, DE < 2^1193·den + 3·2^1193
  obtain ⟨hnumlo, _⟩ := numExpV_bracket hx hC hC0 htnn
  obtain ⟨_, hdenhi⟩ := denExpV_bracket hx hC hC0 htnn
  set num := (evTree x : Int) + int256 (todTree x) with hnumdef
  set den := (evTree x : Int) - int256 (todTree x) with hdendef
  have hden072 : (61251667550081741634933722430035858604 : Int) ≤ den := den_ge_072 hx hC hC0
  have hdenpos : (0:Int) < den := lt_of_lt_of_le (by norm_num) hden072
  have hdenR : (0:Real) < (den : Real) := by exact_mod_cast hdenpos
  have hden072R : (61251667550081741634933722430035858604 : Real) ≤ (den : Real) := by
    have := (@Int.cast_le Real _ _ _ _ _ _ _).mpr hden072; push_cast at this; linarith [this]
  have hnumloR : (2 ^ 1193 : Real) * (num : Real) ≤ (NE : Real) := by
    have := (@Int.cast_le Real _ _ _ _ _ _ _).mpr hnumlo; push_cast at this; linarith [this]
  have hdenhiR : (DE : Real) < (2 ^ 1193 : Real) * (den : Real) + 3 * 2 ^ 1193 := by
    have := (@Int.cast_lt Real _ _ _ _ _ _ _).mpr hdenhi; push_cast at this; linarith [this]
  have hsqrt2_val : Real.sqrt 2 ≤ 14143 / 10000 := by
    rw [Real.sqrt_le_iff]; constructor <;> norm_num
  have hsqrt2_nn : (0:Real) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hMp_le : Mp ≤ 14144 / 14143 := by
    rw [hMpdef, div_le_div_iff₀ (by norm_num) (by norm_num)]
    have h130 : (14144 : Real) ≤ 2 ^ 130 := by
      rw [show (2:Real) ^ 130 = 1361129467683753853853498429727072845824 from by norm_num]; norm_num
    nlinarith [h130]
  have hsM_le : Real.sqrt 2 * Mp ≤ 14144 / 10000 := by
    have hMpnn : (0:Real) ≤ Mp := by rw [hMpdef]; positivity
    calc Real.sqrt 2 * Mp ≤ (14143 / 10000) * (14144 / 14143) :=
          mul_le_mul hsqrt2_val hMp_le hMpnn (by norm_num)
      _ = 14144 / 10000 := by norm_num
  -- NE ≤ √2·Mp·DE ≤ (14144/10000)·DE
  have hNE_le : (NE : Real) ≤ Real.sqrt 2 * Mp * (DE : Real) := by
    have h1 : (NE : Real) ≤ Et * Mp * (DE : Real) := by
      have := mul_le_mul_of_nonneg_right hNEDE_le (le_of_lt hDEpos)
      rwa [div_mul_cancel₀ _ (ne_of_gt hDEpos)] at this
    have h2 : Et * Mp * (DE : Real) ≤ Real.sqrt 2 * Mp * (DE : Real) := by
      apply mul_le_mul_of_nonneg_right _ (le_of_lt hDEpos)
      exact mul_le_mul_of_nonneg_right hEtsqrt2 (le_of_lt hMp_pos)
    linarith [h1, h2]
  -- num ≤ (14144/10000)·(den+3)
  have hnum_le : (num : Real) ≤ (14144 / 10000) * ((den : Real) + 3) := by
    have hp : (0:Real) < (2 ^ 1193 : Real) := by positivity
    rw [← mul_le_mul_left hp]
    calc (2 ^ 1193 : Real) * (num : Real) ≤ (NE : Real) := hnumloR
      _ ≤ Real.sqrt 2 * Mp * (DE : Real) := hNE_le
      _ ≤ (14144 / 10000) * ((2 ^ 1193 : Real) * (den : Real) + 3 * 2 ^ 1193) := by
          calc Real.sqrt 2 * Mp * (DE : Real)
              ≤ (14144 / 10000) * (DE : Real) := mul_le_mul_of_nonneg_right hsM_le (le_of_lt hDEpos)
            _ ≤ (14144 / 10000) * ((2 ^ 1193 : Real) * (den : Real) + 3 * 2 ^ 1193) :=
                mul_le_mul_of_nonneg_left (le_of_lt hdenhiR) (by norm_num)
      _ = (2 ^ 1193 : Real) * ((14144 / 10000) * ((den : Real) + 3)) := by ring
  -- 100·num ≤ 145·den as Real:  100·(14144/10000)(den+3) ≤ 145·den ⟺ den huge
  have hkey : (100 : Real) * (num : Real) ≤ 145 * (den : Real) := by
    have h1 : (100 : Real) * (num : Real) ≤ 100 * ((14144 / 10000) * ((den : Real) + 3)) :=
      mul_le_mul_of_nonneg_left hnum_le (by norm_num)
    nlinarith [h1, hden072R]
  have : ((100 * num : Int) : Real) ≤ ((145 * den : Int) : Real) := by push_cast; linarith [hkey]
  exact_mod_cast this

/-- `r0` is bracketed on the nonneg half: `2¹²⁶ ≤ r0 ≤ 1.45·2¹²⁶` (so `2¹²⁶+r0 ≤ 2.45·2¹²⁶`). -/
theorem r0_bracket_nonneg {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htnn : 0 ≤ int256 (tTree x)) :
    (2 : Int) ^ 126 ≤ int256 (r0Tree x) ∧
      100 * (int256 (r0Tree x)) ≤ 145 * 2 ^ 126 := by
  obtain ⟨hfloor_lo, hfloor_hi⟩ := r0_floor_sandwich hx hC hC0
  have h145 := num_le_145_den hx hC hC0 htnn
  set r0 := int256 (r0Tree x) with hr0def
  set ev := (evTree x : Int) with hevdef
  set tod := int256 (todTree x) with htoddef
  have hden072 : (61251667550081741634933722430035858604 : Int) ≤ ev - tod := by
    have := den_ge_072 hx hC hC0; rw [← hevdef, ← htoddef] at this; exact this
  have hdenpos : (0:Int) < ev - tod := lt_of_lt_of_le (by norm_num) hden072
  -- tod ≥ 0 on nonneg half
  have htodnn : (0:Int) ≤ tod := by
    obtain ⟨_, _, htodlo, _⟩ := todTree_bound hx hC hC0
    have hodnn : (0:Int) ≤ (odTree x : Int) := Int.natCast_nonneg _
    have htod : (2 ^ 128 : Int) * tod ≤ int256 (tTree x) * (odTree x : Int) := htodlo
    have hpos : (0:Int) ≤ int256 (tTree x) * (odTree x : Int) := mul_nonneg htnn hodnn
    nlinarith [htod, hpos]
  refine ⟨?_, ?_⟩
  · -- 2^126 ≤ r0:  2^126·num < (r0+1)·den, num ≥ den ⟹ 2^126·den < (r0+1)·den ⟹ 2^126 < r0+1
    have hnumden : (2:Int)^126 * (ev - tod) ≤ 2 ^ 126 * (ev + tod) := by nlinarith [htodnn]
    have h : (2:Int)^126 * (ev - tod) < (r0 + 1) * (ev - tod) := lt_of_le_of_lt hnumden hfloor_hi
    have := lt_of_mul_lt_mul_right h (le_of_lt hdenpos)
    omega
  · -- 100·r0 ≤ 145·2^126:  100·r0·den ≤ 100·2^126·num ≤ 2^126·145·den
    have h1 : 100 * (r0 * (ev - tod)) ≤ 100 * (2 ^ 126 * (ev + tod)) :=
      mul_le_mul_of_nonneg_left hfloor_lo (by norm_num)
    have h2 : (2:Int)^126 * (100 * (ev + tod)) ≤ 2 ^ 126 * (145 * (ev - tod)) :=
      mul_le_mul_of_nonneg_left h145 (by positivity)
    have hchain : 100 * r0 * (ev - tod) ≤ 145 * 2 ^ 126 * (ev - tod) := by nlinarith [h1, h2]
    exact le_of_mul_le_mul_right hchain hdenpos

/-- **Joint cert-ratio under (nonneg half):** `2¹²⁶·NE − r0·DE ≤ 7·DE`. The shared even truncation
`Ee·(2¹²⁶−r0) ≤ 0` (since `r0 ≥ 2¹²⁶`) is dropped; the floor `2¹²⁶·num − r0·den < den` gives the
`2¹¹⁹³·den` term, and the binding tod truncation `Et' ≤ (2¹¹⁹³ + W_od·2¹⁰³⁹·t)·(2¹²⁶+r0)` is small
because `t ≤ H128` is far below `2¹²⁸`. -/
theorem r0_certRatio_under_nonneg {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htnn : 0 ≤ int256 (tTree x)) :
    2 ^ 126 * evalPoly ExpCertV.numExpV (int256 (tTree x)) -
        int256 (r0Tree x) * evalPoly ExpCertV.denExpV (int256 (tTree x)) ≤
      7 * evalPoly ExpCertV.denExpV (int256 (tTree x)) := by
  obtain ⟨hfloor_lo, hfloor_hi⟩ := r0_floor_sandwich hx hC hC0
  obtain ⟨hevlo, _⟩ := evNumVPoly_bracket hx hC hC0
  have htodub := todNumV_ub hx hC hC0 htnn
  obtain ⟨hr0lo, hr0hi145⟩ := r0_bracket_nonneg hx hC hC0 htnn
  obtain ⟨hdenlo, _⟩ := denExpV_bracket hx hC hC0 htnn
  have hDElb := denExpV_lb hx hC hC0 htnn
  rw [evalNumExpV, evalDenExpV]
  set t := int256 (tTree x) with htdef
  set r0 := int256 (r0Tree x) with hr0def
  set ev := (evTree x : Int) with hevdef
  set tod := int256 (todTree x) with htoddef
  set evP := evalPoly ExpCertV.evNumVPoly t with hevP
  set todP := evalPoly ExpCertV.todNumV t with htodP
  set DE := evP - todP with hDEdef
  -- 2^126·NE − r0·DE = evP·(2^126−r0) + todP·(2^126+r0)
  -- = 2^1193·[2^126·num − r0·den] + Ee·(2^126−r0) + Et'·(2^126+r0)
  --   ≤ 2^1193·den + 0 + (2^1193 + W·2^1039·t)·(2^126+r0)
  have hden072 : (61251667550081741634933722430035858604 : Int) ≤ ev - tod := by
    have := den_ge_072 hx hC hC0; rw [← hevdef, ← htoddef] at this; exact this
  have hdenpos : (0:Int) < ev - tod := lt_of_lt_of_le (by norm_num) hden072
  have h2126r0_np : (2:Int) ^ 126 - r0 ≤ 0 := by linarith [hr0lo]
  have hr0p_nn : (0:Int) ≤ 2 ^ 126 + r0 := by linarith [hr0lo]
  -- evP·(2^126−r0) ≤ 2^1193·ev·(2^126−r0)  (evP ≥ 2^1193·ev, factor ≤ 0)
  have hterm1 : evP * (2 ^ 126 - r0) ≤ 2 ^ 1193 * ev * (2 ^ 126 - r0) :=
    mul_le_mul_of_nonpos_right hevlo h2126r0_np
  -- todP·(2^126+r0) ≤ (2^1193·tod + 2^1193 + W·2^1039·t)·(2^126+r0)  (todP upper, factor ≥ 0)
  have hterm2 : todP * (2 ^ 126 + r0) ≤
      (2 ^ 1193 * tod + 2 ^ 1193 + 69402657 * 2 ^ 1039 * t) * (2 ^ 126 + r0) :=
    mul_le_mul_of_nonneg_right htodub hr0p_nn
  -- floor: 2^126·num − r0·den < den, scaled by 2^1193:  2^1193·(2^126·num − r0·den) < 2^1193·den
  have hfloor_lt : (2:Int) ^ 126 * (ev + tod) - r0 * (ev - tod) < (ev - tod) := by linarith [hfloor_hi]
  have hfloor1193 : (2 ^ 1193 : Int) * ((2:Int) ^ 126 * (ev + tod) - r0 * (ev - tod)) <
      2 ^ 1193 * (ev - tod) := by
    have := mul_lt_mul_of_pos_left hfloor_lt (by positivity : (0:Int) < 2 ^ 1193); linarith [this]
  -- combine: 2^126·NE − r0·DE ≤ 2^1193·den + (2^1193 + W·2^1039·t)·(2^126+r0)
  have hcombine : 2 ^ 126 * (evP + todP) - r0 * DE ≤
      2 ^ 1193 * (ev - tod) + (2 ^ 1193 + 69402657 * 2 ^ 1039 * t) * (2 ^ 126 + r0) := by
    have hid1 : 2 ^ 126 * (evP + todP) - r0 * DE = evP * (2 ^ 126 - r0) + todP * (2 ^ 126 + r0) := by
      rw [hDEdef]; ring
    have hid2 : 2 ^ 1193 * ev * (2 ^ 126 - r0) + (2 ^ 1193 * tod + 2 ^ 1193 + 69402657 * 2 ^ 1039 * t) * (2 ^ 126 + r0)
        = 2 ^ 1193 * ((2:Int) ^ 126 * (ev + tod) - r0 * (ev - tod))
          + (2 ^ 1193 + 69402657 * 2 ^ 1039 * t) * (2 ^ 126 + r0) := by ring
    rw [hid1]; linarith [hterm1, hterm2, hfloor1193, hid2]
  -- now bound the RHS ≤ 6·DE.
  -- (A) 2^1193·den ≤ DE + 32·2^1193 (denExpV hi), and 32·2^1193 ≤ DE (DE > 2^1317):  2^1193·den ≤ 2·DE
  have hden2 : 2 ^ 1193 * (ev - tod) ≤ DE + 32 * 2 ^ 1193 := by
    rw [hDEdef, evalDenExpV] at *; linarith [hdenlo]
  have h32 : (32 : Int) * 2 ^ 1193 ≤ DE := by
    have hD1317 : (2:Int)^1317 < DE := by rw [hDEdef, evalDenExpV] at *; linarith [hDElb]
    have : (32 : Int) * 2 ^ 1193 < 2 ^ 1317 := by
      rw [show (32:Int) * 2 ^ 1193 = 2 ^ 1198 from by rw [show (32:Int)=2^5 from by norm_num, ← pow_add]]
      exact pow_lt_pow_right₀ (by norm_num) (by norm_num)
    linarith [this, hD1317]
  have hAterm : 2 ^ 1193 * (ev - tod) ≤ 2 * DE := by linarith [hden2, h32]
  -- (B) (2^1193 + W·2^1039·t)·(2^126+r0) ≤ 4·DE.   bound via t ≤ H128, 2^126+r0 ≤ 2.45·2^126.
  have hDElb' : (2:Int)^1317 < DE := by rw [hDEdef, evalDenExpV] at *; linarith [hDElb]
  obtain ⟨_, hthi⟩ := tTree_in_cert_domain hx hC hC0
  have htH : t ≤ 117932881612756647068972071382077242199 := hthi
  -- 2^126 + r0 ≤ 2.45·2^126, i.e. 100·(2^126+r0) ≤ 245·2^126
  have hr0p_bound : 100 * (2 ^ 126 + r0) ≤ 245 * 2 ^ 126 := by linarith [hr0hi145]
  have hBterm : (2 ^ 1193 + 69402657 * 2 ^ 1039 * t) * (2 ^ 126 + r0) ≤ 5 * DE := by
    have hDEden : 2 ^ 1193 * (ev - tod) - 32 * 2 ^ 1193 ≤ DE := by
      rw [hDEdef, evalDenExpV] at *; linarith [hdenlo]
    have hden_lo : (61251667550081741634933722430035858604 : Int) ≤ ev - tod := by
      have := den_ge_072 hx hC hC0; rw [← hevdef, ← htoddef] at this; exact this
    -- 2^1193 + W·2^1039·t ≤ 2^1193 + W·2^1039·H128 (t ≤ H128, t ≥ 0)
    have hcoeff : 2 ^ 1193 + 69402657 * 2 ^ 1039 * t ≤
        2 ^ 1193 + 69402657 * 2 ^ 1039 * 117932881612756647068972071382077242199 := by
      have := mul_le_mul_of_nonneg_left htH (by positivity : (0:Int) ≤ 69402657 * 2 ^ 1039); linarith [this]
    have hC0nn : (0:Int) ≤ 2 ^ 1193 + 69402657 * 2 ^ 1039 * 117932881612756647068972071382077242199 := by positivity
    have hLHS : (2 ^ 1193 + 69402657 * 2 ^ 1039 * t) * (2 ^ 126 + r0) ≤
        (2 ^ 1193 + 69402657 * 2 ^ 1039 * 117932881612756647068972071382077242199) * (2 ^ 126 + r0) :=
      mul_le_mul_of_nonneg_right hcoeff hr0p_nn
    -- 100·(C0·(2^126+r0)) ≤ C0·245·2^126
    have hLHS2 : 100 * ((2 ^ 1193 + 69402657 * 2 ^ 1039 * 117932881612756647068972071382077242199) * (2 ^ 126 + r0)) ≤
        (2 ^ 1193 + 69402657 * 2 ^ 1039 * 117932881612756647068972071382077242199) * (245 * 2 ^ 126) := by
      have h := mul_le_mul_of_nonneg_left hr0p_bound hC0nn
      have hid : (2 ^ 1193 + 69402657 * 2 ^ 1039 * 117932881612756647068972071382077242199) * (100 * (2 ^ 126 + r0))
          = 100 * ((2 ^ 1193 + 69402657 * 2 ^ 1039 * 117932881612756647068972071382077242199) * (2 ^ 126 + r0)) := by ring
      have hid2 : (2 ^ 1193 + 69402657 * 2 ^ 1039 * 117932881612756647068972071382077242199) * (245 * 2 ^ 126)
          = (2 ^ 1193 + 69402657 * 2 ^ 1039 * 117932881612756647068972071382077242199) * (245 * 2 ^ 126) := rfl
      linarith [h, hid]
    -- key integer cert (common 2^1165 scale): C0·245·2^126 ≤ 500·(2^1193·(den−32)).
    have hkey : (2 ^ 1193 + 69402657 * 2 ^ 1039 * 117932881612756647068972071382077242199) * (245 * 2 ^ 126) ≤
        500 * (2 ^ 1193 * (ev - tod) - 32 * 2 ^ 1193) := by
      -- factor everything to the common 2^1165 scale and compare coefficients
      have hA : (2:Int) ^ 1193 * 2 ^ 126 = 2 ^ 154 * 2 ^ 1165 := by rw [← pow_add, ← pow_add]
      have hpe2 : (2:Int) ^ 1039 * 2 ^ 126 = 2 ^ 1165 := by rw [← pow_add]
      have hpe3 : (2:Int) ^ 1193 = 2 ^ 28 * 2 ^ 1165 := by rw [← pow_add]
      have hp : (0:Int) < (2:Int) ^ 1165 := by positivity
      -- the coefficient inequality, scaled by 2^1165
      have hcoeff_le : (245 * 2 ^ 154 + 245 * 69402657 * 117932881612756647068972071382077242199 : Int) ≤
          500 * 2 ^ 28 * ((ev - tod) - 32) := by
        have h154 : (2:Int)^154 = 22835963083295358096932575511191922182123945984 := by norm_num
        have h28 : (2:Int)^28 = 268435456 := by norm_num
        rw [h154, h28]; linarith [hden_lo]
      have hscaled := mul_le_mul_of_nonneg_right hcoeff_le (le_of_lt hp)
      -- rewrite both sides to the (·)·2^1165 form
      calc (2 ^ 1193 + 69402657 * 2 ^ 1039 * 117932881612756647068972071382077242199) * (245 * 2 ^ 126)
          = (245 * 2 ^ 154 + 245 * 69402657 * 117932881612756647068972071382077242199) * 2 ^ 1165 := by
            linear_combination (245 : Int) * hA + (245 * 69402657 * 117932881612756647068972071382077242199 : Int) * hpe2
        _ ≤ (500 * 2 ^ 28 * ((ev - tod) - 32)) * 2 ^ 1165 := hscaled
        _ = 500 * (2 ^ 1193 * (ev - tod) - 32 * 2 ^ 1193) := by
            linear_combination (-500 * ((ev - tod) - 32) : Int) * hpe3
    -- LHS ≤ C0·(2^126+r0); 100·that ≤ C0·245·2^126 ≤ 500·(2^1193 den − 32·2^1193) ≤ 500·DE; so LHS ≤ 5·DE
    have h500 : (500 : Int) * (2 ^ 1193 * (ev - tod) - 32 * 2 ^ 1193) ≤ 500 * DE := by linarith [hDEden]
    linarith [hLHS, hLHS2, hkey, h500]
  linarith [hcombine, hAterm, hBterm]

/-- **The joint per-point deficit (nonneg half).** `2¹²⁶·exp(rt) ≤ r0 + 8`. From the joint
cert-ratio under (`2¹²⁶·NE − r0·DE ≤ 7·DE`), the not-too-below cert (`exp ≤ (NE/DE)·M⁺`), and the
under-direction gap-1 (`exp(rt) ≤ √2`, `rt − t/2¹²⁸ < 33/(32·2¹²⁸)`). -/
theorem r0_real_under_tight {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htnn : 0 ≤ int256 (tTree x)) :
    (2 ^ 126 : Real) * Real.exp (reducedArg x) ≤ (int256 (r0Tree x) : Real) + 8 := by
  have hunder := r0_certRatio_under_nonneg hx hC hC0 htnn
  obtain ⟨_, hthi⟩ := tTree_in_cert_domain hx hC hC0
  set t := int256 (tTree x) with htdef
  have htdom : t ≤ (ExpCertV.H128 : Int) := by
    rw [show ((ExpCertV.H128 : Nat) : Int) = 117932881612756647068972071382077242199 from by
      unfold ExpCertV.H128; norm_num]
    exact hthi
  have hDElb := denExpV_lb hx hC hC0 htnn
  set NE := evalPoly ExpCertV.numExpV t with hNEdef
  set DE := evalPoly ExpCertV.denExpV t with hDEdef
  have hDEpos_int : (0 : Int) < DE := by
    have : (0:Int) < 2 ^ 1317 := by positivity
    linarith [hDElb, this]
  have hDEpos : (0 : Real) < (DE : Real) := by exact_mod_cast hDEpos_int
  set r0 := int256 (r0Tree x) with hr0def
  -- 2^126·NE/DE ≤ r0 + 7
  have hunderR : (2 ^ 126 : Real) * (NE : Real) - (r0 : Real) * (DE : Real) ≤ 7 * (DE : Real) := by
    have := (@Int.cast_le Real _ _ _ _ _ _ _).mpr hunder; push_cast at this; linarith [this]
  have hr0_ge : (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) ≤ (r0 : Real) + 7 := by
    rw [mul_div_assoc', div_le_iff₀ hDEpos]; nlinarith [hunderR, hDEpos]
  -- certUp: exp(t/2^128) ≤ (NE/DE)·Mpp
  have hcertup := certUp_real htnn htdom
  have hNEnn : (0 : Real) ≤ (NE : Real) := by
    have := certNE_nonneg htnn htdom; exact_mod_cast this
  set Et := Real.exp ((t : Real) / (2 ^ 128 : Real)) with hEtdef
  set Mpp : Real := (2 ^ 130 + 1 : Real) / (2 ^ 130 : Real) with hMppdef
  have hEt_le : Et ≤ ((NE : Real) / (DE : Real)) * Mpp := by
    have hc : Et ≤ ((2 ^ 130 + 1 : Int) : Real) * (NE : Real) /
        (((2 ^ 130 : Int) : Real) * (DE : Real)) := hcertup
    rw [hMppdef]
    have key : ((NE : Real) / (DE : Real)) * ((2 ^ 130 + 1 : Real) / (2 ^ 130 : Real)) =
        ((2 ^ 130 + 1 : Int) : Real) * (NE : Real) / (((2 ^ 130 : Int) : Real) * (DE : Real)) := by
      push_cast; field_simp; ring
    rw [key]; exact hc
  have hNEDE_nn : (0 : Real) ≤ (NE : Real) / (DE : Real) := div_nonneg hNEnn (le_of_lt hDEpos)
  have hMpp1 : Mpp - 1 = 1 / (2 ^ 130 : Real) := by rw [hMppdef]; field_simp
  -- Et ≤ √2 (nonneg half)
  have hEtsqrt2 := exp_t_le_sqrt2 hx hC hC0 htnn
  rw [← hEtdef] at hEtsqrt2
  have hsqrt2_val : Real.sqrt 2 ≤ 14143 / 10000 := by rw [Real.sqrt_le_iff]; constructor <;> norm_num
  have hsqrt2_nn : (0:Real) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  -- 2^126·Et ≤ 2^126·(NE/DE)·Mpp = 2^126·(NE/DE) + 2^126·(NE/DE)·(Mpp−1) ≤ (r0+7) + 1/4
  have hEt_bound : (2 ^ 126 : Real) * Et ≤ (r0 : Real) + 7 + 3 / 10 := by
    have h1 : (2 ^ 126 : Real) * Et ≤ (2 ^ 126 : Real) * (((NE : Real) / (DE : Real)) * Mpp) :=
      mul_le_mul_of_nonneg_left hEt_le (by positivity)
    have h2 : (2 ^ 126 : Real) * (((NE : Real) / (DE : Real)) * Mpp) =
        (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) +
          (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) * (Mpp - 1) := by ring
    -- 2^126·(NE/DE)·(Mpp−1) ≤ 3/10.  NE/DE·2^126 ≤ r0+7 ≤ 2^128+7;  ·(1/2^130) ≈ 1/4 < 3/10.
    have h3 : (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) * (Mpp - 1) ≤ 3 / 10 := by
      rw [hMpp1]
      obtain ⟨_, hr0hi⟩ := r0Tree_bounds hx hC hC0
      have hr0R : (r0 : Real) < (2 ^ 128 : Real) := by
        have h := (@Int.cast_lt Real _ _ _ _ _ _ _).mpr hr0hi
        rw [show ((2 ^ 128 : Int) : Real) = (2 ^ 128 : Real) from by push_cast; ring] at h; exact h
      have hpos : (0:Real) ≤ (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) := mul_nonneg (by positivity) hNEDE_nn
      have hlt : (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) < (2 ^ 128 : Real) + 7 := by
        linarith [hr0_ge, hr0R]
      calc (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) * (1 / (2 ^ 130 : Real))
          ≤ ((2 ^ 128 : Real) + 7) * (1 / (2 ^ 130 : Real)) :=
            mul_le_mul_of_nonneg_right (le_of_lt hlt) (by positivity)
        _ ≤ 3 / 10 := by norm_num
    linarith [h1, h2 ▸ h1, h3, hr0_ge]
  -- gap-1 (under, tight): Ert − Et ≤ (rt − t/2^128)·Ert, rt − t/2^128 < 33/(32·2^128), Ert ≤ 2
  set Ert := Real.exp (reducedArg x) with hErtdef
  have hgapunder := reducedArg_close_under hx hC hC0
  have hExp_diff : Ert - Et ≤ (reducedArg x - (t : Real) / (2 ^ 128 : Real)) * Ert := exp_diff_le _ _
  have hErt_le_two := exp_reducedArg_le_two hx hC hC0
  rw [← hErtdef] at hErt_le_two
  have hErt_nn : (0:Real) ≤ Ert := le_of_lt (Real.exp_pos _)
  have hgap126 : (2 ^ 126 : Real) * (Ert - Et) ≤ 6 / 10 := by
    have hgap : Ert - Et ≤ (33 / (32 * (2 ^ 128 : Real))) * Ert :=
      le_trans hExp_diff (mul_le_mul_of_nonneg_right (le_of_lt hgapunder) hErt_nn)
    have h1 : (2 ^ 126 : Real) * (Ert - Et) ≤ (2 ^ 126 : Real) * ((33 / (32 * (2 ^ 128 : Real))) * Ert) :=
      mul_le_mul_of_nonneg_left hgap (by positivity)
    have h2 : (2 ^ 126 : Real) * ((33 / (32 * (2 ^ 128 : Real))) * Ert) ≤
        (2 ^ 126 : Real) * ((33 / (32 * (2 ^ 128 : Real))) * 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hErt_le_two (by positivity)) (by positivity)
    have h3 : (2 ^ 126 : Real) * ((33 / (32 * (2 ^ 128 : Real))) * 2) ≤ 6 / 10 := by norm_num
    linarith [h1, h2, h3]
  -- assemble: 2^126·Ert = 2^126·Et + 2^126·(Ert−Et) ≤ (r0+7+1/4) + 6/10 < r0 + 8
  have hdist : (2 ^ 126 : Real) * Ert = (2 ^ 126 : Real) * Et + (2 ^ 126 : Real) * (Ert - Et) := by ring
  show (2 ^ 126 : Real) * Ert ≤ (r0 : Real) + 8
  linarith [hEt_bound, hgap126, hdist]

/-- `r0 ≤ 2¹²⁶` on the negative half (num ≤ den ⟺ tod ≤ 0). -/
theorem r0_le_2126_neg {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htneg : int256 (tTree x) ≤ 0) :
    int256 (r0Tree x) ≤ 2 ^ 126 := by
  obtain ⟨hfloor_lo, _⟩ := r0_floor_sandwich hx hC hC0
  set r0 := int256 (r0Tree x) with hr0def
  set ev := (evTree x : Int) with hevdef
  set tod := int256 (todTree x) with htoddef
  have hden072 : (61251667550081741634933722430035858604 : Int) ≤ ev - tod := by
    have := den_ge_072 hx hC hC0; rw [← hevdef, ← htoddef] at this; exact this
  have hdenpos : (0:Int) < ev - tod := lt_of_lt_of_le (by norm_num) hden072
  have htodnp : tod ≤ 0 := by
    obtain ⟨_, _, htodlo, _⟩ := todTree_bound hx hC hC0
    have hodnn : (0:Int) ≤ (odTree x : Int) := Int.natCast_nonneg _
    have : int256 (tTree x) * (odTree x : Int) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg htneg hodnn
    nlinarith [htodlo, this]
  -- r0·den ≤ 2^126·num ≤ 2^126·den (num ≤ den)
  have hnumden : r0 * (ev - tod) ≤ 2 ^ 126 * (ev - tod) := by
    have h1 : r0 * (ev - tod) ≤ 2 ^ 126 * (ev + tod) := hfloor_lo
    nlinarith [h1, htodnp, (by positivity : (0:Int) ≤ (2:Int)^126)]
  exact le_of_mul_le_mul_right hnumden hdenpos

/-- **Joint cert-ratio under (negative half):** `2¹²⁶·NE − r0·DE ≤ 6·DE`. The binding even
truncation `Ee·(2¹²⁶−r0)` (small factor) and the tod truncation `Et'·(2¹²⁶+r0)` both fit. -/
theorem r0_certRatio_under_neg {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htneg : int256 (tTree x) ≤ 0) :
    2 ^ 126 * evalPoly ExpCertV.numExpV (int256 (tTree x)) -
        int256 (r0Tree x) * evalPoly ExpCertV.denExpV (int256 (tTree x)) ≤
      7 * evalPoly ExpCertV.denExpV (int256 (tTree x)) := by
  obtain ⟨_, hfloor_hi⟩ := r0_floor_sandwich hx hC hC0
  obtain ⟨hevlo, hevhi⟩ := evNumVPoly_bracket hx hC hC0
  obtain ⟨_, htodhi⟩ := todNumV_bracket_neg hx hC hC0 htneg
  have hr0le := r0_le_2126_neg hx hC hC0 htneg
  obtain ⟨hr0lo, _⟩ := r0Tree_bounds hx hC hC0
  obtain ⟨hdenlo, _⟩ := denExpV_bracket_neg hx hC hC0 htneg
  have hDElb := denExpV_lb_neg hx hC hC0 htneg
  rw [evalNumExpV, evalDenExpV]
  set t := int256 (tTree x) with htdef
  set r0 := int256 (r0Tree x) with hr0def
  set ev := (evTree x : Int) with hevdef
  set tod := int256 (todTree x) with htoddef
  set evP := evalPoly ExpCertV.evNumVPoly t with hevP
  set todP := evalPoly ExpCertV.todNumV t with htodP
  set DE := evP - todP with hDEdef
  have hden_lo : (61251667550081741634933722430035858604 : Int) ≤ ev - tod := by
    have := den_ge_072 hx hC hC0; rw [← hevdef, ← htoddef] at this; exact this
  -- on the neg half tod ≤ 0, so den = ev − tod ≥ ev ≥ A4
  have htod_np : tod ≤ 0 := by
    obtain ⟨_, _, htodlo, _⟩ := todTree_bound hx hC hC0
    have hodnn : (0:Int) ≤ (odTree x : Int) := Int.natCast_nonneg _
    have hp : t * (odTree x : Int) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg htneg hodnn
    have h2 : (2 ^ 128 : Int) * tod ≤ 2 ^ 128 * 0 := by simpa using le_trans htodlo hp
    exact le_of_mul_le_mul_left h2 (by norm_num)
  have hden_A4 : (103786963415199049567855548359006885036 : Int) ≤ ev - tod := by
    obtain ⟨hevlo', _⟩ := evTree_facts (vTree_eq hx hC hC0).2
    have hev : (103786963415199049567855548359006885036 : Int) ≤ ev := by
      rw [hevdef]; have : (0x4e14a45e8ec305e233e11b4174e214ac : Int) ≤ (evTree x : Int) := by exact_mod_cast hevlo'
      rw [show (0x4e14a45e8ec305e233e11b4174e214ac : Int) = 103786963415199049567855548359006885036 from by norm_num] at this
      exact this
    linarith [hev, htod_np]
  have h2126r0_nn : (0:Int) ≤ 2 ^ 126 - r0 := by linarith [hr0le]
  have hr0p_nn : (0:Int) ≤ 2 ^ 126 + r0 := by linarith [hr0lo]
  -- Ee = evP − 2^1193·ev ∈ [0, W_ev).  evP·(2^126−r0) ≤ (2^1193·ev + W_ev)·(2^126−r0)
  have hterm1 : evP * (2 ^ 126 - r0) ≤ (2 ^ 1193 * ev + 1130577 * 2 ^ 1173) * (2 ^ 126 - r0) :=
    mul_le_mul_of_nonneg_right (le_of_lt hevhi) h2126r0_nn
  -- Et' = todP − 2^1193·tod < 2·2^1193 ⟹ todP < 2^1193·tod + 2·2^1193; todP·(2^126+r0) ≤ (2^1193·tod+2·2^1193)·(2^126+r0)
  have hterm2 : todP * (2 ^ 126 + r0) ≤ (2 ^ 1193 * tod + 2 * 2 ^ 1193) * (2 ^ 126 + r0) :=
    mul_le_mul_of_nonneg_right (le_of_lt htodhi) hr0p_nn
  -- floor: 2^126·num − r0·den < den ⟹ 2^1193·(2^126·num − r0·den) < 2^1193·den
  have hfloor_lt : (2:Int) ^ 126 * (ev + tod) - r0 * (ev - tod) < (ev - tod) := by linarith [hfloor_hi]
  have hfloor1193 : (2 ^ 1193 : Int) * ((2:Int) ^ 126 * (ev + tod) - r0 * (ev - tod)) <
      2 ^ 1193 * (ev - tod) := by
    have := mul_lt_mul_of_pos_left hfloor_lt (by positivity : (0:Int) < 2 ^ 1193); linarith [this]
  -- combine: 2^126·NE − r0·DE ≤ 2^1193·den + W_ev·(2^126−r0) + 2·2^1193·(2^126+r0)
  have hcombine : 2 ^ 126 * (evP + todP) - r0 * DE ≤
      2 ^ 1193 * (ev - tod) + 1130577 * 2 ^ 1173 * (2 ^ 126 - r0) + 2 * 2 ^ 1193 * (2 ^ 126 + r0) := by
    have hid1 : 2 ^ 126 * (evP + todP) - r0 * DE = evP * (2 ^ 126 - r0) + todP * (2 ^ 126 + r0) := by
      rw [hDEdef]; ring
    have hid2 : (2 ^ 1193 * ev + 1130577 * 2 ^ 1173) * (2 ^ 126 - r0)
        + (2 ^ 1193 * tod + 2 * 2 ^ 1193) * (2 ^ 126 + r0)
        = 2 ^ 1193 * ((2:Int) ^ 126 * (ev + tod) - r0 * (ev - tod))
          + 1130577 * 2 ^ 1173 * (2 ^ 126 - r0) + 2 * 2 ^ 1193 * (2 ^ 126 + r0) := by ring
    rw [hid1]; linarith [hterm1, hterm2, hfloor1193, hid2]
  -- bound RHS by 6·DE.  DE ≥ 2^1193·(den−2), den ≥ den_lo.
  have hDEden : 2 ^ 1193 * (ev - tod) - 2 * 2 ^ 1193 ≤ DE := by
    rw [hDEdef, evalDenExpV] at *; linarith [hdenlo]
  -- (A) 2^1193·den ≤ DE + 2·2^1193 ≤ 2·DE  (32·2^1193... no, 2·2^1193 ≤ DE since DE>2^1317)
  have hD1317 : (2:Int)^1317 < DE := by rw [hDEdef, evalDenExpV] at *; linarith [hDElb]
  have h2 : (2 : Int) * 2 ^ 1193 ≤ DE := by
    have he : (2 : Int) * 2 ^ 1193 = 2 ^ 1194 := by rw [show (1194:Nat) = 1193 + 1 from rfl, pow_succ]; ring
    have : (2 : Int) * 2 ^ 1193 < 2 ^ 1317 := by
      rw [he]; exact pow_lt_pow_right₀ (by norm_num) (by norm_num)
    linarith [this, hD1317]
  have hAterm : 2 ^ 1193 * (ev - tod) ≤ 2 * DE := by
    have hden2 : 2 ^ 1193 * (ev - tod) ≤ DE + 2 * 2 ^ 1193 := by linarith [hDEden]
    linarith [hden2, h2]
  -- (B) W_ev·(2^126−r0) ≤ 2·DE  (2^126−r0 ≤ 2^126;  W_ev·2^126 = 1130577·2^1299;  vs 2·DE ≥ 2·2^1193·(den−2))
  have hBterm : (1130577 : Int) * 2 ^ 1173 * (2 ^ 126 - r0) ≤ 1 * DE := by
    have hle : (1130577 : Int) * 2 ^ 1173 * (2 ^ 126 - r0) ≤ 1130577 * 2 ^ 1173 * 2 ^ 126 :=
      mul_le_mul_of_nonneg_left (by linarith [hr0lo]) (by positivity)
    -- 1130577·2^1173·2^126 = 1130577·2^1299 ; DE ≥ 2^1193·(den−2);  1130577·2^106 ≤ (den−2)
    have hkey : (1130577 : Int) * 2 ^ 1173 * 2 ^ 126 ≤ 1 * (2 ^ 1193 * (ev - tod) - 2 * 2 ^ 1193) := by
      have hA : (2:Int) ^ 1173 * 2 ^ 126 = 2 ^ 106 * 2 ^ 1193 := by rw [← pow_add, ← pow_add]
      have hp : (0:Int) < (2:Int) ^ 1193 := by positivity
      have heL : (1130577 : Int) * 2 ^ 1173 * 2 ^ 126 = (1130577 * 2 ^ 106) * 2 ^ 1193 := by
        have e : (1130577 : Int) * 2 ^ 1173 * 2 ^ 126 = 1130577 * (2 ^ 1173 * 2 ^ 126) := by ring
        rw [e, hA]; ring
      have heR : (1 : Int) * (2 ^ 1193 * (ev - tod) - 2 * 2 ^ 1193) = (1 * ((ev - tod) - 2)) * 2 ^ 1193 := by ring
      rw [heL, heR, mul_le_mul_right hp]
      have h106 : (1130577 * 2 ^ 106 : Int) = 91723303209870778371580046068760444928 := by norm_num
      calc (1130577 * 2 ^ 106 : Int) = 91723303209870778371580046068760444928 := h106
        _ ≤ 1 * ((ev - tod) - 2) := by linarith [hden_A4]
    linarith [hle, hkey]
  -- (C) 2·2^1193·(2^126+r0) ≤ 2·DE.  (2^126+r0) ≤ 2·2^126 (r0 ≤ 2^126); 2·2^1193·2·2^126 = 4·2^1319; vs 2·DE.
  have hCterm : (2 : Int) * 2 ^ 1193 * (2 ^ 126 + r0) ≤ 4 * DE := by
    have hle : (2 : Int) * 2 ^ 1193 * (2 ^ 126 + r0) ≤ 2 * 2 ^ 1193 * (2 ^ 126 + 2 ^ 126) :=
      mul_le_mul_of_nonneg_left (by linarith [hr0le]) (by positivity)
    have hkey : (2 : Int) * 2 ^ 1193 * (2 ^ 126 + 2 ^ 126) ≤ 4 * (2 ^ 1193 * (ev - tod) - 2 * 2 ^ 1193) := by
      have hA : (2:Int) ^ 1193 * 2 ^ 126 = 2 ^ 1319 := by rw [← pow_add]
      have hp : (0:Int) < (2:Int) ^ 1193 := by positivity
      -- LHS = 2·2^1193·2·2^126 = 4·2^1319 = (4·2^126)·2^1193;  RHS = 2·((den)−2)·2^1193
      have heL : (2 : Int) * 2 ^ 1193 * (2 ^ 126 + 2 ^ 126) = (4 * 2 ^ 126) * 2 ^ 1193 := by ring
      have heR : (4 : Int) * (2 ^ 1193 * (ev - tod) - 2 * 2 ^ 1193) = (4 * ((ev - tod) - 2)) * 2 ^ 1193 := by ring
      rw [heL, heR, mul_le_mul_right hp]
      have h126 : (4 * 2 ^ 126 : Int) = 340282366920938463463374607431768211456 := by norm_num
      calc (4 * 2 ^ 126 : Int) = 340282366920938463463374607431768211456 := h126
        _ ≤ 4 * ((ev - tod) - 2) := by linarith [hden_A4]
    linarith [hle, hkey]
  linarith [hcombine, hAterm, hBterm, hCterm]

/-- **Per-point deficit (tight, negative half).** `2¹²⁶·exp(rt) ≤ r0 + 8` for `t ≤ 0`. -/
theorem r0_real_under_tight_neg {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htneg : int256 (tTree x) ≤ 0) :
    (2 ^ 126 : Real) * Real.exp (reducedArg x) ≤ (int256 (r0Tree x) : Real) + 8 := by
  have hunder := r0_certRatio_under_neg hx hC hC0 htneg
  have htdom := tdom_neg hx hC hC0 htneg
  set t := int256 (tTree x) with htdef
  have hDElb := denExpV_lb_neg hx hC hC0 htneg
  set NE := evalPoly ExpCertV.numExpV t with hNEdef
  set DE := evalPoly ExpCertV.denExpV t with hDEdef
  have hDEpos_int : (0 : Int) < DE := by
    have : (0:Int) < 2 ^ 1317 := by positivity
    linarith [hDElb, this]
  have hDEpos : (0 : Real) < (DE : Real) := by exact_mod_cast hDEpos_int
  set r0 := int256 (r0Tree x) with hr0def
  have hunderR : (2 ^ 126 : Real) * (NE : Real) - (r0 : Real) * (DE : Real) ≤ 7 * (DE : Real) := by
    have := (@Int.cast_le Real _ _ _ _ _ _ _).mpr hunder; push_cast at this; linarith [this]
  have hr0_ge : (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) ≤ (r0 : Real) + 7 := by
    rw [mul_div_assoc', div_le_iff₀ hDEpos]; nlinarith [hunderR, hDEpos]
  -- certUp_real_neg: exp(t/2^128) ≤ (NE/DE)·Mp, Mp = 2^130/(2^130−1)
  have hcu := certUp_real_neg htneg htdom
  obtain ⟨hNEpos, _⟩ := certNE_pos_neg_aux htneg htdom
  have hNEnn : (0 : Real) ≤ (NE : Real) := by have : (0:Int) ≤ NE := le_of_lt hNEpos
                                              exact_mod_cast this
  set Et := Real.exp ((t : Real) / (2 ^ 128 : Real)) with hEtdef
  set Mp : Real := (2 ^ 130 : Real) / ((2 ^ 130 : Real) - 1) with hMpdef
  have hEt_le : Et ≤ ((NE : Real) / (DE : Real)) * Mp := by
    rw [hMpdef]
    have key : ((NE : Real) / (DE : Real)) * ((2 ^ 130 : Real) / ((2 ^ 130 : Real) - 1)) =
        ((2 ^ 130 : Int) : Real) * (NE : Real) / (((2 ^ 130 - 1 : Int) : Real) * (DE : Real)) := by
      push_cast; field_simp; ring
    rw [key]; exact hcu
  have hNEDE_nn : (0 : Real) ≤ (NE : Real) / (DE : Real) := div_nonneg hNEnn (le_of_lt hDEpos)
  have hMp1 : Mp - 1 = 1 / ((2 ^ 130 : Real) - 1) := by rw [hMpdef]; field_simp
  -- 2^126·Et ≤ 2^126·(NE/DE)·Mp = 2^126·(NE/DE) + 2^126·(NE/DE)·(Mp−1) ≤ (r0+6) + 1/4
  have hEt_bound : (2 ^ 126 : Real) * Et ≤ (r0 : Real) + 7 + 3 / 10 := by
    have h1 : (2 ^ 126 : Real) * Et ≤ (2 ^ 126 : Real) * (((NE : Real) / (DE : Real)) * Mp) :=
      mul_le_mul_of_nonneg_left hEt_le (by positivity)
    have h2 : (2 ^ 126 : Real) * (((NE : Real) / (DE : Real)) * Mp) =
        (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) +
          (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) * (Mp - 1) := by ring
    have h3 : (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) * (Mp - 1) ≤ 3 / 10 := by
      rw [hMp1]
      obtain ⟨_, hr0hi⟩ := r0Tree_bounds hx hC hC0
      have hr0R : (r0 : Real) < (2 ^ 128 : Real) := by
        have h := (@Int.cast_lt Real _ _ _ _ _ _ _).mpr hr0hi
        rw [show ((2 ^ 128 : Int) : Real) = (2 ^ 128 : Real) from by push_cast; ring] at h; exact h
      have hpos : (0:Real) ≤ (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) := mul_nonneg (by positivity) hNEDE_nn
      have hlt : (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) < (2 ^ 128 : Real) + 7 := by
        linarith [hr0_ge, hr0R]
      calc (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) * (1 / ((2 ^ 130 : Real) - 1))
          ≤ ((2 ^ 128 : Real) + 7) * (1 / ((2 ^ 130 : Real) - 1)) :=
            mul_le_mul_of_nonneg_right (le_of_lt hlt) (by positivity)
        _ ≤ 3 / 10 := by norm_num
    linarith [h1, h2 ▸ h1, h3, hr0_ge]
  -- gap-1 (under, tight)
  set Ert := Real.exp (reducedArg x) with hErtdef
  have hgapunder := reducedArg_close_under hx hC hC0
  have hExp_diff : Ert - Et ≤ (reducedArg x - (t : Real) / (2 ^ 128 : Real)) * Ert := exp_diff_le _ _
  have hErt_le_two := exp_reducedArg_le_two hx hC hC0
  rw [← hErtdef] at hErt_le_two
  have hErt_nn : (0:Real) ≤ Ert := le_of_lt (Real.exp_pos _)
  have hgap126 : (2 ^ 126 : Real) * (Ert - Et) ≤ 6 / 10 := by
    have hgap : Ert - Et ≤ (33 / (32 * (2 ^ 128 : Real))) * Ert :=
      le_trans hExp_diff (mul_le_mul_of_nonneg_right (le_of_lt hgapunder) hErt_nn)
    have h1 : (2 ^ 126 : Real) * (Ert - Et) ≤ (2 ^ 126 : Real) * ((33 / (32 * (2 ^ 128 : Real))) * Ert) :=
      mul_le_mul_of_nonneg_left hgap (by positivity)
    have h2 : (2 ^ 126 : Real) * ((33 / (32 * (2 ^ 128 : Real))) * Ert) ≤
        (2 ^ 126 : Real) * ((33 / (32 * (2 ^ 128 : Real))) * 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hErt_le_two (by positivity)) (by positivity)
    have h3 : (2 ^ 126 : Real) * ((33 / (32 * (2 ^ 128 : Real))) * 2) ≤ 6 / 10 := by norm_num
    linarith [h1, h2, h3]
  have hdist : (2 ^ 126 : Real) * Ert = (2 ^ 126 : Real) * Et + (2 ^ 126 : Real) * (Ert - Et) := by ring
  show (2 ^ 126 : Real) * Ert ≤ (r0 : Real) + 8
  linarith [hEt_bound, hgap126, hdist]

/-- **Per-point deficit (tight, any sign):** `2¹²⁶·exp(rt) ≤ r0 + 8`. -/
theorem r0_real_under_within {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    (2 ^ 126 : Real) * Real.exp (reducedArg x) ≤ (int256 (r0Tree x) : Real) + 8 := by
  rcases le_or_gt 0 (int256 (tTree x)) with htnn | htneg
  · exact r0_real_under_tight hx hC hC0 htnn
  · exact r0_real_under_tight_neg hx hC hC0 (le_of_lt htneg)

end ExpYul
